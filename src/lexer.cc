// Copyright 2022 Matt Rudary

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "emil/lexer.h"

#include <fmt/core.h>
#include <sys/errno.h>
#include <unicode/bytestream.h>
#include <unicode/errorcode.h>
#include <unicode/normalizer2.h>
#include <unicode/uchar.h>
#include <unicode/urename.h>
#include <unicode/uscript.h>
#include <unicode/utypes.h>
#include <utf8.h>

#include <algorithm>
#include <cassert>
#include <charconv>
#include <coroutine>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iterator>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <type_traits>  // IWYU pragma: keep
#include <utility>
#include <variant>
#include <vector>

#include "emil/misc.h"
#include "emil/processor.h"
#include "emil/strconvert.h"
#include "emil/text_input.h"
#include "emil/token.h"

namespace emil {

LexingError::LexingError(std::string msg, const Location& location,
                         std::u32string partial_token_text)
    : msg(std::move(msg)),
      location(location),
      partial_token_text(std::move(partial_token_text)),
      full_msg(fmt::format("{}:{}: error: {}", this->location.filename,
                           this->location.line, this->msg)) {}

namespace {

template <typename It>
class U8ByteSink : public icu::ByteSink {
 public:
  explicit U8ByteSink(It sink) : sink_(sink) {}

  void Append(const char* data, int32_t n) override {
    sink_ = std::copy_n(data, n, sink_);
  }

 private:
  It sink_;
};

bool is_whitespace(char32_t c) {
  return u_hasBinaryProperty(c, UCHAR_PATTERN_WHITE_SPACE);
}

bool is_decimal_digit(char32_t c) { return '0' <= c && c <= '9'; }

bool is_hex_digit(char32_t c) {
  return is_decimal_digit(c) || ('a' <= c && c <= 'f') ||
         ('A' <= c && c <= 'F');
}

bool is_octal_digit(char32_t c) { return '0' <= c && c <= '7'; }

bool is_binary_digit(char32_t c) { return c == '0' || c == '1'; }

bool can_start_operator(char32_t c) {
  if (c > 127) {
    const auto mask = U_GET_GC_MASK(c);
    return mask & (U_GC_P_MASK | U_GC_S_MASK);
  } else {
    switch (c) {
      case '!':
      case '#':
      case '$':
      case '%':
      case '&':
      case '*':
      case '+':
      case '-':
      case '/':
      case ':':
      case '<':
      case '=':
      case '>':
      case '?':
      case '@':
      case '\\':
      case '^':
      case '|':
      case '~':
        return true;
      default:
        return false;
    }
  }
}

constexpr std::u8string_view KW_INF = u8"Inf";
constexpr std::u8string_view KW_NAN = u8"NaN";
constexpr std::u8string_view KW_AND = u8"and";
constexpr std::u8string_view KW_AS = u8"as";
constexpr std::u8string_view KW_CASE = u8"case";
constexpr std::u8string_view KW_DATATYPE = u8"datatype";
constexpr std::u8string_view KW_ELSE = u8"else";
constexpr std::u8string_view KW_END = u8"end";
constexpr std::u8string_view KW_EXCEPTION = u8"exception";
constexpr std::u8string_view KW_FN = u8"fn";
constexpr std::u8string_view KW_FUN = u8"fun";
constexpr std::u8string_view KW_HANDLE = u8"handle";
constexpr std::u8string_view KW_IF = u8"if";
constexpr std::u8string_view KW_IMPLICIT = u8"implicit";
constexpr std::u8string_view KW_IN = u8"in";
constexpr std::u8string_view KW_INFIX = u8"infix";
constexpr std::u8string_view KW_INFIXR = u8"infixr";
constexpr std::u8string_view KW_LET = u8"let";
constexpr std::u8string_view KW_LOCAL = u8"local";
constexpr std::u8string_view KW_NONFIX = u8"nonfix";
constexpr std::u8string_view KW_OF = u8"of";
constexpr std::u8string_view KW_OPEN = u8"open";
constexpr std::u8string_view KW_PREFIX = u8"prefix";
constexpr std::u8string_view KW_RAISE = u8"raise";
constexpr std::u8string_view KW_REC = u8"rec";
constexpr std::u8string_view KW_THEN = u8"then";
constexpr std::u8string_view KW_TYPE = u8"type";
constexpr std::u8string_view KW_UNDERSCORE = u8"_";
constexpr std::u8string_view KW_VAL = u8"val";
constexpr std::u8string_view KW_WHILE = u8"while";
constexpr std::u8string_view KW_WITHTYPE = u8"withtype";

bool match_rest(std::u8string_view keyword, const std::u8string& token,
                std::size_t prefix) {
  return keyword.size() == token.size() &&
         token.ends_with(keyword.substr(prefix));
}

constexpr std::u8string_view COLON = u8":";
constexpr std::u8string_view PIPE = u8"|";
constexpr std::u8string_view TO_EXPR = u8"=>";
constexpr std::u8string_view TO_TYPE = u8"->";
constexpr std::u8string_view HASH = u8"#";
constexpr std::u8string_view EQUALS = u8"=";
constexpr std::u8string_view ASTERISK = u8"*";

void match_keyword_in_id_op(Token& token) {
#define REPLACE(kw)              \
  if (match_rest(kw, name, 1)) { \
    token.type = TokenType::kw;  \
    return;                      \
  }
  const std::u8string& name = get<std::u8string>(token.aux);
  switch (name[0]) {
    case ':':
      REPLACE(COLON);
      return;

    case '|':
      REPLACE(PIPE);
      return;

    case '=':
      REPLACE(EQUALS);
      REPLACE(TO_EXPR);
      return;

    case '-':
      REPLACE(TO_TYPE);
      return;

    case '#':
      REPLACE(HASH);
      return;

    case '*':
      REPLACE(ASTERISK);
      return;
  }
#undef REPLACE
}

void match_keyword_and_tyvar_in_id_word(Token& token) {
#define REPLACE(kw, prefix)           \
  if (match_rest(kw, name, prefix)) { \
    token.type = TokenType::kw;       \
    token.aux = {};                   \
    return;                           \
  }
  const auto& name = get<std::u8string>(token.aux);
  switch (name[0]) {
    case '\'':
      if (name.size() == 1)
        throw LexingError("\"'\" is not a valid identifier.", token.location,
                          token.text);
      token.type = TokenType::ID_TYPE;
      return;

    case 'I':
      if (match_rest(KW_INF, name, 1)) {
        token.type = TokenType::FPLITERAL;
        token.aux = std::numeric_limits<double>::infinity();
      }
      return;

    case 'N':
      if (match_rest(KW_NAN, name, 1)) {
        token.type = TokenType::FPLITERAL;
        token.aux = std::numeric_limits<double>::quiet_NaN();
      }
      return;

    case 'a':
      REPLACE(KW_AND, 1);
      REPLACE(KW_AS, 1);
      return;

    case 'c':
      REPLACE(KW_CASE, 1);
      return;

    case 'd':
      REPLACE(KW_DATATYPE, 1);
      return;

    case 'e':
      REPLACE(KW_ELSE, 1);
      REPLACE(KW_END, 1);
      REPLACE(KW_EXCEPTION, 1);
      return;

    case 'f':
      REPLACE(KW_FN, 1);
      REPLACE(KW_FUN, 1);
      return;

    case 'h':
      REPLACE(KW_HANDLE, 1);
      return;

    case 'i':
      if (name.starts_with(u8"infix")) {
        REPLACE(KW_INFIX, 5);
        REPLACE(KW_INFIXR, 5);
      } else {
        REPLACE(KW_IF, 1);
        REPLACE(KW_IMPLICIT, 1);
        REPLACE(KW_IN, 1);
      }
      return;

    case 'l':
      REPLACE(KW_LET, 1);
      REPLACE(KW_LOCAL, 1);
      return;

    case 'n':
      REPLACE(KW_NONFIX, 1);
      return;

    case 'o':
      REPLACE(KW_OF, 1);
      REPLACE(KW_OPEN, 1);
      return;

    case 'p':
      REPLACE(KW_PREFIX, 1);
      return;

    case 'r':
      REPLACE(KW_RAISE, 1);
      REPLACE(KW_REC, 1);
      return;

    case 't':
      REPLACE(KW_THEN, 1);
      REPLACE(KW_TYPE, 1);
      return;

    case 'v':
      REPLACE(KW_VAL, 1);
      return;

    case 'w':
      REPLACE(KW_WHILE, 1);
      REPLACE(KW_WITHTYPE, 1);
      return;

    case '_':
      REPLACE(KW_UNDERSCORE, 1);
      return;
  }
#undef REPLACE
}

Token make_qualified_id(std::u32string text, const Location& location,
                        std::vector<std::u8string>& qualifiers, Token id) {
  text += id.text;
  TokenType type;
  switch (id.type) {
    case TokenType::ID_WORD:
      type = TokenType::QUAL_ID_WORD;
      break;

    case TokenType::ID_OP:
    case TokenType::EQUALS:
    case TokenType::ASTERISK:
      type = TokenType::QUAL_ID_OP;
      break;

    default:
      throw LexingError(
          fmt::format("Illegal token type in qualified identifier: {}",
                      id.type),
          location, text);
  }

  return {.text = std::move(text),
          .location = location,
          .type = type,
          .aux = QualifiedIdentifier{.qualifiers = std::move(qualifiers),
                                     .id = get<std::u8string>(id.aux)}};
}

using processor::eof;
using processor::Expected;
using processor::next_input;
using processor::reset;
using processor::subtask;

using CharPtr = processor::detail::input_traits<char32_t>::peek_type;

class LexerUnicodeError : public icu::ErrorCode {
 public:
  explicit LexerUnicodeError(const Location& location) : location_(location) {}
  ~LexerUnicodeError() override {
    // This will cause the program to terminate, so handle your failures.
    if (isFailure()) handleFailure();
  }

  void handleFailure() const final;

 private:
  const Location location_;
};

enum class StringType {
  SIMPLE,  // "string"
  TRIPLE,  // """string"""
  RAW,     // r"delim(string)delim"
};

enum class FormatString {
  NO,
  START,
  CONTINUE,
};

}  // namespace

struct lexer_impl {
  const std::string filename;
  bool requires_more_input = false;
  int start_line = 1;
  int line_number = 1;
  std::u32string current_token;

  processor::processor<char32_t, Expected<Token>> stream_tokens(
      bool toplevel = true) {
    bool needs_sync = false;
    bool saved_prev_token_was_lparen = false;
    std::size_t brace_depth = 1;

    while (true) {
      try {
        if (needs_sync) {
          co_await sync();
          needs_sync = false;
        }
        std::exception_ptr eptr;
        try {
          assert(!toplevel || !requires_more_input);
          co_await skip_whitespace();
          current_token.clear();
          start_line = line_number;
          const bool prev_token_was_lparen = saved_prev_token_was_lparen;
          saved_prev_token_was_lparen = false;

          const char32_t c = co_await peek();

          if (!c) {
            if (!toplevel) {
              throw LexingError("End of file while processing format string",
                                {filename, start_line}, current_token);
            }
            co_yield make_token(TokenType::END_OF_FILE);
            co_return;
          }

          requires_more_input = true;

          if (is_decimal_digit(c)) {
            co_yield complete(co_await consume_number());
            continue;
          }

          switch (c) {
            case '-':
              if (is_decimal_digit(co_await peek(2))) {
                co_yield complete(co_await consume_number());
                continue;
              } else if (co_await peek(2) == 'I' && co_await peek(3) == 'n' &&
                         co_await peek(4) == 'f') {
                co_await advance();
                co_await advance();
                co_await advance();
                co_await advance();
                co_yield complete(
                    make_token(TokenType::FPLITERAL,
                               -std::numeric_limits<double>::infinity()));
                continue;
              }
              break;

            case '#':
              if (co_await peek(2) == '"') {
                co_yield complete(co_await consume_char());
                continue;
              }
              break;

            case '"': {
              StringType type;
              if (co_await peek(2) == '"' && co_await peek(3) == '"') {
                type = StringType::TRIPLE;
              } else {
                type = StringType::SIMPLE;
              }
              auto s = consume_string(type, false).as_subprocess();
              while (!co_await s.done()) co_yield complete(co_await s);
              continue;
            }

            case 'f':
            case 'F': {
              StringType type;
              const char32_t next = co_await peek(2);
              if ((next == 'r' || next == 'R') && co_await peek(3) == '"') {
                type = StringType::RAW;
              } else if (next == '"') {
                if (co_await peek(3) == '"' && co_await peek(4) == '"') {
                  type = StringType::TRIPLE;
                } else {
                  type = StringType::SIMPLE;
                }
              } else {
                break;
              }
              auto s = consume_string(type, true).as_subprocess();
              while (!co_await s.done()) co_yield complete(co_await s);
              continue;
            }

            case 'r':
            case 'R':
              if (co_await peek(2) == '"') {
                auto s = consume_string(StringType::RAW, false).as_subprocess();
                while (!co_await s.done()) co_yield complete(co_await s);
                continue;
              }
              break;

            case '*':
              if (co_await peek(2) == ')' && !prev_token_was_lparen)
                error("Comment end outside of comment.");
              break;

            case '(':
              if (co_await peek(2) == '*' && co_await peek(3) != ')') {
                co_await skip_comment();
                requires_more_input = false;
                continue;
              }
              co_await advance();
              co_yield complete(make_token(TokenType::LPAREN));
              saved_prev_token_was_lparen = true;
              continue;

            case ')':
              co_await advance();
              co_yield complete(make_token(TokenType::RPAREN));
              continue;

            case '[':
              co_await advance();
              co_yield complete(make_token(TokenType::LBRACKET));
              continue;

            case ']':
              co_await advance();
              co_yield complete(make_token(TokenType::RBRACKET));
              continue;

            case '{':
              ++brace_depth;
              co_await advance();
              co_yield complete(make_token(TokenType::LBRACE));
              continue;

            case '}':
              if (--brace_depth == 0) {
                co_return;
              }
              co_await advance();
              co_yield complete(make_token(TokenType::RBRACE));
              continue;

            case ',':
              co_await advance();
              co_yield complete(make_token(TokenType::COMMA));
              continue;

            case ';':
              co_await advance();
              co_yield complete(make_token(TokenType::SEMICOLON));
              continue;

            case '.':
              if (is_decimal_digit(co_await peek(2))) {
                error("Floating point constants must start with a digit.");
              }
              co_await advance();
              if (co_await match('.') && co_await match('.')) {
                co_yield complete(make_token(TokenType::ELLIPSIS));
                continue;
              }
              error("Stray '.'.");
          }

          co_yield complete(co_await consume_identifier());
        } catch (LexingError& err) {
          if (toplevel) {
            eptr = std::make_exception_ptr(err);
          } else {
            throw;
          }
        }
        if (eptr) {
          co_yield complete(eptr);
          needs_sync = true;
        }
      } catch (reset) {
        if (!toplevel) throw;
        requires_more_input = false;
        needs_sync = true;
      } catch (eof) {
        throw std::logic_error("Unexpected eof");
        break;
      }
    }
  }

  explicit lexer_impl(std::string filename) : filename(std::move(filename)) {}

  template <typename T>
  T&& complete(T&& t) {
    requires_more_input = false;
    return std::forward<T>(t);
  }

  Token make_token(TokenType type, token_auxiliary_t aux = {}) {
    return Token{.text = std::move(current_token),
                 .location = {filename, start_line},
                 .type = type,
                 .aux = std::move(aux)};
  }

  [[noreturn]] void error(std::string msg) const {
    throw LexingError(std::move(msg), {filename, start_line}, current_token);
  }

  subtask<char32_t, char32_t> peek(std::size_t i = 1) {
    auto c = co_await processor::peek{i};
    if (c)
      co_return *c;
    else
      co_return 0;
  }

  subtask<char32_t, char32_t> advance() {
    const char32_t c = co_await next_input{};
    current_token.push_back(c);
    if (c == '\n') ++line_number;
    co_return c;
  }

  subtask<char32_t, char32_t> advance_safe(const char* part_of_speech) {
    if (!co_await peek())
      error(fmt::format("End of file reached while tokenizing {}",
                        part_of_speech));
    co_return co_await advance();
  }

  subtask<char32_t, void> sync() {
    while (true) {
      const auto c = co_await peek();
      if (!c) co_return;
      co_await advance();
      if (c == '\n') co_return;
    }
  }

  subtask<char32_t, bool> match(char32_t expected) {
    if (co_await peek() == expected) {
      co_await advance();
      co_return true;
    }
    co_return false;
  }

  subtask<char32_t, void> consume(char32_t expected,
                                  const char* part_of_speech) {
    const char32_t c = co_await advance_safe(part_of_speech);
    if (c != expected) {
      error(fmt::format("Expected '{}' but got '{}' while tokenizing {}",
                        to_std_string(expected), to_std_string(c),
                        part_of_speech));
    }
  }

  subtask<char32_t, void> skip_whitespace() {
    while (is_whitespace(co_await peek())) co_await advance();
  }

  subtask<char32_t, void> skip_comment() {
    int level = 1;
    co_await consume('(', "comment");
    co_await consume('*', "comment");
    while (co_await peek()) {
      const char32_t c = co_await advance();
      if (c == '*') {
        if (co_await peek() == ')') {
          co_await advance();
          if (!--level) co_return;
        }
      } else if (c == '(' && co_await peek() == '*') {
        co_await advance();
        ++level;
      }
    }
    error("File ended mid-comment.");
  }

  bool can_start_word(char32_t c) {
    LexerUnicodeError err({filename, line_number});

    if (c == '_' || c == '\'') return true;
    if (u_hasBinaryProperty(c, UCHAR_XID_START) &&
        uscript_getUsage(uscript_getScript(c, err)) ==
            USCRIPT_USAGE_RECOMMENDED) {
      return true;
    }
    err.assertSuccess();
    return false;
  }

  bool can_continue_word(char32_t c) {
    LexerUnicodeError err({filename, line_number});
    if (can_start_word(c)) return true;
    if (u_hasBinaryProperty(c, UCHAR_XID_CONTINUE) &&
        uscript_getUsage(uscript_getScript(c, err)) ==
            USCRIPT_USAGE_RECOMMENDED) {
      return true;
    }
    err.assertSuccess();
    return false;
  }

  std::u8string normalize(std::u8string&& s) {
    LexerUnicodeError err({filename, line_number});
    const icu::Normalizer2* const normalizer =
        icu::Normalizer2::getNFCInstance(err);
    err.assertSuccess();
    if (normalizer->isNormalizedUTF8(s, err)) {
      return std::move(s);
    }
    std::u8string n;
    U8ByteSink sink(back_inserter(n));
    normalizer->normalizeUTF8(0, s, sink, nullptr, err);
    err.assertSuccess();
    return n;
  }

  subtask<char32_t, Token> consume_id_op() {
    while (can_start_operator(co_await peek())) {
      co_await append_next_grapheme_cluster(current_token);
    }
    std::u8string identifier;
    utf8::utf32to8(begin(current_token), end(current_token),
                   back_inserter(identifier));
    auto t = make_token(TokenType::ID_OP, normalize(std::move(identifier)));
    match_keyword_in_id_op(t);
    co_return t;
  }

  subtask<char32_t, Token> consume_id_word() {
    std::u8string identifier;
    auto it = back_inserter(identifier);
    assert(can_start_word(co_await peek()));
    it = utf8::append(co_await advance(), it);
    while (can_continue_word(co_await peek())) {
      utf8::append(co_await advance(), it);
    }
    auto t = make_token(TokenType::ID_WORD, normalize(std::move(identifier)));
    match_keyword_and_tyvar_in_id_word(t);
    co_return t;
  }

  subtask<char32_t, Token> consume_identifier() {
    std::u32string text;
    std::optional<Location> location;
    std::vector<std::u8string> qualifiers;
    char32_t first_char = co_await peek();
    while (true) {
      if (can_start_operator(first_char)) {
        if (qualifiers.empty()) {
          co_return co_await consume_id_op();
        } else {
          co_return make_qualified_id(std::move(text), *location, qualifiers,
                                      co_await consume_id_op());
        }
      }

      if (!can_start_word(first_char)) {
        error(fmt::format("Illegal token starting with '{}'",
                          to_std_string(first_char)));
      }

      Token t = co_await consume_id_word();
      current_token.clear();
      co_await skip_whitespace();

      if (!co_await match('.')) {
        co_return qualifiers.empty()
            ? t
            : make_qualified_id(std::move(text), *location, qualifiers,
                                std::move(t));
      }

      if (t.type != TokenType::ID_WORD) {
        error("Keywords are illegal as part of qualified identifiers");
      }
      if (!location) location = t.location;
      qualifiers.push_back(std::move(get<std::u8string>(t.aux)));
      text += t.text;
      co_await skip_whitespace();
      text += current_token;
      current_token.clear();
      first_char = co_await peek();
    }
  }

  subtask<char32_t, Token> consume_number() {
    std::string number;
    char32_t first_char = co_await advance();
    if (first_char == '-') {
      number += '-';
      first_char = co_await advance();
    }
    if (first_char == '0') {
      if (co_await match('x') || co_await match('X')) {
        co_return co_await consume_integer(number, is_hex_digit, 16);
      } else if (co_await match('o') || co_await match('O')) {
        co_return co_await consume_integer(number, is_octal_digit, 8);
      } else if (co_await match('b') || co_await match('B')) {
        co_return co_await consume_integer(number, is_binary_digit, 2);
      }
    }
    number += first_char;
    co_await consume_digits(number, is_decimal_digit);

    if (co_await match('.')) {
      co_return co_await consume_fp_from_decimal(number);
    } else if (co_await match('e') || co_await match('E')) {
      co_return co_await consume_fp_from_exponent(number);
    } else if (co_await match('f') || co_await match('F')) {
      co_return consume_fp(number);
    }
    co_return co_await consume_integer(number, is_decimal_digit, 10);
  }

  template <typename Pred>
  subtask<char32_t, void> consume_digits(std::string& number, Pred&& is_digit) {
    enum { DIGIT, UNDERSCORE, NONE } state = NONE;
    if (!number.empty()) {
      if (is_digit(number.back())) {
        state = DIGIT;
      } else if (number.back() == '_') {
        state = UNDERSCORE;
      }
    }
    while (const char32_t c = co_await peek()) {
      if (is_digit(c)) {
        state = DIGIT;
        number += static_cast<char>(co_await advance());
      } else if (c == '_') {
        if (state != DIGIT) {
          error("In numeric literal, '_' must follow a digit.");
        }
        state = UNDERSCORE;
        co_await advance();
      } else {
        break;
      }
    }
    if (state == UNDERSCORE) {
      error("Numeric constant may not end with '_'");
    }
  }

  template <typename Pred>
  subtask<char32_t, Token> consume_integer(std::string& number, Pred&& is_digit,
                                           int base) {
    co_await consume_digits(number, std::forward<Pred>(is_digit));
    const bool is_int = co_await match('i') || co_await match('I');

    if (const char32_t c = co_await peek()) {
      if (c == '.' || can_continue_word(c)) {
        error(fmt::format("Illegal digit '{}' in literal with base {}",
                          to_std_string(c), base));
      }
    }
    if (is_int) {
      std::int64_t value;
      const char* last = number.data() + number.size();
      const auto result = std::from_chars(number.data(), last, value, base);
      if (result.ec != std::errc{}) {
        if (result.ec == std::errc::result_out_of_range) {
          error(
              "Integer constant could not be represented by a 64-bit signed "
              "integer.");
        } else {
          auto code = std::make_error_code(result.ec);
          throw std::logic_error(
              fmt::format("Unexpected error parsing a number: {}: {}",
                          code.category().name(), code.value()));
        }
      }
      if (result.ptr != last) {
        throw std::logic_error("Error parsing integer constant.");
      }
      co_return make_token(TokenType::ILITERAL, value);
    } else {
      co_return make_token(
          TokenType::ILITERAL,
          BigintLiteralData{std::u8string(number.begin(), number.end()), base});
    }
  }

  Token consume_fp(std::string& number) {
    char* last;
    errno = 0;
    double value = std::strtod(number.data(), &last);
    if (errno == ERANGE) {
      error("Floating point constant could not be represented by double.");
    }
    if (last != number.data() + number.size()) {
      throw std::logic_error("Error parsing floating point constant.");
    }
    return make_token(TokenType::FPLITERAL, value);
  }

  subtask<char32_t, Token> consume_fp_from_exponent(std::string& number) {
    number += 'e';
    bool has_digit = false;
    if (co_await match('-')) {
      number += '-';
    } else if (co_await match('+')) {
      number += '+';
    }
    while (co_await peek() && is_decimal_digit(co_await peek())) {
      has_digit = true;
      number += co_await advance();
    }
    if (!has_digit) {
      error("Floating point exponent has no digits.");
    }
    co_return consume_fp(number);
  }

  subtask<char32_t, Token> consume_fp_from_decimal(std::string& number) {
    number += '.';
    co_await consume_digits(number, is_decimal_digit);
    if (co_await match('e') || co_await match('E')) {
      co_return co_await consume_fp_from_exponent(number);
    } else {
      co_await match('f') || co_await match('F');
      co_return consume_fp(number);
    }
  }

  subtask<char32_t, uint_fast8_t> consume_hex_digit() {
    char32_t c = co_await advance_safe("hexadecimal constant");
    if ('0' <= c && c <= '9') {
      co_return c - '0';
    } else if ('a' <= c && c <= 'f') {
      co_return 10 + c - 'a';
    } else if ('A' <= c && c <= 'F') {
      co_return 10 + c - 'A';
    } else {
      error(fmt::format("Illegal hex digit '{}'.", to_std_string(c)));
    }
  }

  subtask<char32_t, char32_t> consume_short_unicode_escape() {
    char32_t val = co_await consume_hex_digit() << 12;
    val += co_await consume_hex_digit() << 8;
    val += co_await consume_hex_digit() << 4;
    val += co_await consume_hex_digit();
    if (0xD800 <= val && val <= 0xDFFF) {
      error(fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
    }
    co_return val;
  }

  subtask<char32_t, char32_t> consume_long_unicode_escape() {
    char32_t val = co_await consume_hex_digit() << 20;
    val += co_await consume_hex_digit() << 16;
    val += co_await consume_hex_digit() << 12;
    val += co_await consume_hex_digit() << 8;
    val += co_await consume_hex_digit() << 4;
    val += co_await consume_hex_digit();
    if ((0xD800 <= val && val <= 0xDFFF) || 0x10FFFF < val) {
      error(fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
    }
    co_return val;
  }

  subtask<char32_t, char32_t> consume_escape() {
    co_await consume('\\', "character escape");
    switch (const char32_t c = co_await advance_safe("character escape")) {
      case '"':
      case '\\':
      case '$':
        co_return c;

      case 'a':
        co_return '\a';
      case 'b':
        co_return '\b';
      case 'f':
        co_return '\f';
      case 'n':
        co_return '\n';
      case 'r':
        co_return '\r';
      case 't':
        co_return '\t';
      case 'v':
        co_return '\v';
      case '^': {
        char32_t cc = co_await advance_safe("character escape");
        if (cc < 64 || 95 < cc)
          error(fmt::format("Illegal escape code '\\^{}'.", to_std_string(cc)));
        co_return cc - 64;
      }
      case 'u':
        co_return co_await consume_short_unicode_escape();
      case 'U':
        co_return co_await consume_long_unicode_escape();
      default:
        error(fmt::format("Illegal escape character '{}'", to_std_string(c)));
    }
  }

  subtask<char32_t, Token> consume_char() {
    char32_t value;
    co_await consume('#', "character");
    co_await consume('"', "character");
    switch (const char32_t c = co_await peek()) {
      case '"':
        error("Empty character constant.");

      case '\\':
        value = co_await consume_escape();
        break;

      default:
        co_await advance();
        value = c;
    }
    if (!co_await match('"')) {
      error("Multi-character character constant.");
    }
    co_return make_token(TokenType::CHAR, value);
  }

  subtask<char32_t, bool> match_end_of_string(
      StringType type, std::u32string_view raw_delimiter) {
    switch (type) {
      case StringType::SIMPLE:
        co_return co_await match('"');

      case StringType::TRIPLE:
        if (co_await peek(3) == '"' && co_await peek(2) == '"' &&
            co_await peek() == '"') {
          co_await advance();
          co_await advance();
          co_await advance();
          co_return true;
        }
        co_return false;

      case StringType::RAW: {
        if (co_await peek() == ')') {
          for (std::size_t i = 0; i < raw_delimiter.size(); ++i) {
            if (co_await peek(i + 2) != raw_delimiter[i]) co_return false;
          }
          if (co_await peek(2 + raw_delimiter.size()) == '"') {
            for (std::size_t i = 0; i < 2 + raw_delimiter.size(); ++i) {
              co_await advance();
            }
            co_return true;
          }
        }
        co_return false;
      }
    }
  }

  subtask<char32_t, void> skip_gap(StringType type) {
    co_await consume('\\', "gap in string");
    if (type != StringType::SIMPLE) {
      error("Gaps only permitted in strings delimited with a single '\"'");
    }
    while (is_whitespace(co_await peek())) {
      co_await advance_safe("gap in string");
    }
    if (!co_await match('\\')) {
      error("Gap must begin and end with '\\' and contain only whitespace");
    }
  }

  subtask<char32_t, std::u32string> consume_raw_delimiter() {
    const auto c = co_await advance();
    assert(c == 'r' || c == 'R');
    co_await consume('"', "raw string literal");
    const auto start = current_token.size();
    for (char32_t c = co_await advance_safe("raw string delimiter"); c != '(';
         c = co_await advance_safe("raw string delimiter")) {
      if (c == ')' || c == '\\' || c == 0 || is_whitespace(c)) {
        error(fmt::format("Illegal character '{}' in raw string delimiter",
                          to_std_string(c)));
      }
    }
    co_return current_token.substr(start, current_token.size() - start - 1);
  }

  processor::processor<char32_t, Token> consume_fstring_substitution() {
    co_await consume('$', "fstring substitution");
    if (co_await match('{')) {
      co_yield make_token(TokenType::FSTRING_IEXPR_S);
      auto sub = stream_tokens(false).as_subprocess();
      while (!co_await sub.done()) {
        auto et = co_await sub;
        co_yield visit(
            overloaded{[](std::exception_ptr&& p) -> Token&& {
                         std::rethrow_exception(p);
                       },
                       [](Token&& t) -> Token&& { return std::move(t); }},
            std::move(et));
      }
      co_await consume('}', "fstring substitution");
      co_yield make_token(TokenType::FSTRING_IEXPR_F);
      co_return;
    }

    Token t = co_await consume_id_word();
    if (t.type != TokenType::ID_WORD) {
      error("Identifier following '$' in format string must not be a keyword.");
    }
    t.type = TokenType::FSTRING_IVAR;
    co_yield t;
  }

  processor::processor<char32_t, Token> consume_string(StringType type,
                                                       bool is_format_string) {
    if (is_format_string) {
      const auto c = co_await advance();
      assert(c == 'f' || c == 'F');
    }

    std::u32string raw_delimiter;
    switch (type) {
      case StringType::RAW:
        raw_delimiter = co_await consume_raw_delimiter();
        break;

      case StringType::SIMPLE:
        co_await consume('"', "string literal");
        break;

      case StringType::TRIPLE:
        co_await consume('"', "string literal");
        co_await consume('"', "string literal");
        co_await consume('"', "string literal");
        break;
    }

    std::u8string contents;
    bool seen_substitution = false;
    auto it = back_inserter(contents);
    while (!co_await match_end_of_string(type, raw_delimiter)) {
      const char32_t c = co_await peek();
      if (!c) {
        error("End of file in string literal");
      } else if (c == '\\' && type != StringType::RAW) {
        if (is_whitespace(co_await peek(2))) {
          co_await skip_gap(type);
        } else {
          utf8::append(co_await consume_escape(), it);
        }
      } else if (is_format_string && c == '$') {
        co_yield make_token(
            seen_substitution ? TokenType::FSTRING_CONT : TokenType::FSTRING,
            std::move(contents));
        contents.clear();
        seen_substitution = true;
        auto sub = consume_fstring_substitution().as_subprocess();
        while (!co_await sub.done()) co_yield co_await sub;
      } else {
        co_await advance();
        if (c == '\n' && type == StringType::SIMPLE) {
          error(
              "Line breaks are not permitted in strings delimited with a "
              "single '\"' except in a gap.");
        }
        utf8::append(c, it);
      }
    }
    co_yield make_token(
        is_format_string
            ? seen_substitution ? TokenType::FSTRING_CONT : TokenType::FSTRING
            : TokenType::STRING,
        std::move(contents));
  }
};

namespace {

void LexerUnicodeError::handleFailure() const {
  throw LexingError(fmt::format("Unicode error: {}", u_errorName(errorCode)),
                    location_, U"");
}

}  // namespace

lexer::lexer(std::string filename)
    : impl_(std::make_unique<lexer_impl>(std::move(filename))) {}

lexer::~lexer() = default;

bool lexer::requires_more_input() const { return impl_->requires_more_input; }

const std::string& lexer::filename() const { return impl_->filename; }

processor::processor<char32_t, Expected<Token>> lexer::lex() {
  return impl_->stream_tokens();
}

processor::processor<char32_t, Expected<Token>> lex(std::string filename) {
  lexer l{std::move(filename)};
  auto p = l.lex().as_subprocess();
  while (!co_await p.done()) {
    co_yield co_await p;
  }
}

}  // namespace emil
