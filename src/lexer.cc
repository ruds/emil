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
#include <gmpxx.h>
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
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <istream>
#include <iterator>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <type_traits>
#include <utility>

#include "emil/source.h"
#include "emil/token.h"
#include "private/single_pass_search.h"

namespace emil {

class UnicodeError : public icu::ErrorCode {
 public:
  explicit UnicodeError(Lexer& lexer) : lexer_(lexer) {}
  ~UnicodeError() override {
    // This will cause the program to terminate, so handle your failures.
    if (isFailure()) handleFailure();
  }

  void handleFailure() const final {
    lexer_.error(fmt::format("Unicode error: {}", u_errorName(errorCode)));
  }

 private:
  Lexer& lexer_;
};

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

std::string char32_to_string(char32_t c) {
  std::u32string_view s(&c, 1);
  return utf8::utf32to8(s);
}

class line_counting_source_iterator {
  struct proxy {
    char32_t value;

    char32_t operator*() const { return value; }
  };

 public:
  using iterator_concept = std::input_iterator_tag;
  using difference_type = std::ptrdiff_t;
  using value_type = char32_t;
  using reference = char32_t;
  using pointer = char32_t*;

  Source* source;
  int* line_number;

  char32_t operator*() const { return *source->peek(); }

  line_counting_source_iterator& operator++() {
    char32_t c = source->advance();
    if (c == '\n') ++*line_number;
    return *this;
  }

  proxy operator++(int) {
    proxy result{source->advance()};
    return result;
  }

  bool operator==(const line_counting_source_iterator& o) const {
    return o.source == source || (!o.source && source->at_end());
  }
};

static_assert(std::input_iterator<line_counting_source_iterator>);

}  // namespace

Lexer::Lexer(std::string filename, std::unique_ptr<Source> source)
    : filename_(std::move(filename)), source_(std::move(source)) {}

Token Lexer::next_token() {
  skip_whitespace();
  current_token_.clear();
  start_line_ = next_line_;

  if (at_end()) return make_token(TokenType::END);

  char32_t c = advance();

  if (is_decimal_digit(c)) {
    return match_number(c);
  }

  switch (c) {
    case '-':
      if (is_decimal_digit(peek())) {
        return match_number(c);
      } else if (peek() == 'I' && peek(1) == 'n' && peek(2) == 'f') {
        advance();
        advance();
        advance();
        return make_token(TokenType::FPLITERAL,
                          -std::numeric_limits<double>::infinity());
      }
      break;

    case '#':
      if (match('"')) return match_char();
      break;

    case '"':
      if (peek() == '"' && peek(1) == '"') {
        advance();
        advance();
        return match_string(StringType::TRIPLE);
      }
      return match_string(StringType::SIMPLE);

    case 'r':
    case 'R':
      if (match('"')) {
        std::u32string delimiter = match_raw_delimiter();
        return match_string(StringType::RAW, delimiter);
      }
      break;

    case 'I':
      if (peek() == 'n' && peek(1) == 'f') {
        advance();
        advance();
        return make_token(TokenType::FPLITERAL,
                          std::numeric_limits<double>::infinity());
      }
      break;

    case 'N':
      if (peek() == 'a' && peek(1) == 'N') {
        advance();
        advance();
        return make_token(TokenType::FPLITERAL,
                          std::numeric_limits<double>::quiet_NaN());
      }
      break;
  }

  return match_identifier(c);
}

void Lexer::advance_past(std::u32string_view substr) {
  dpx::single_pass_search(
      line_counting_source_iterator{source_.get(), &next_line_}, {},
      begin(substr), end(substr));
  if (!source_->at_end()) source_->advance();
}

Token Lexer::make_token(TokenType type, token_auxiliary_t aux) const {
  return Token{.text = std::move(current_token_),
               .line = start_line_,
               .type = type,
               .aux = std::move(aux)};
}

void Lexer::error(std::string msg) {
  throw LexingError(std::move(msg), filename_, start_line_, current_token_);
}

bool Lexer::at_end() const { return source_->at_end(); }

char32_t Lexer::advance() {
  current_token_.push_back(source_->advance());
  return current_token_.back();
}

char32_t Lexer::advance_safe(const char* part_of_speech) {
  if (at_end()) {
    error(
        fmt::format("End of file reached while tokenizing {}", part_of_speech));
  }
  return advance();
}

char32_t Lexer::peek(size_t lookahead) const {
  if (auto next = source_->peek(lookahead)) {
    return *next;
  } else {
    return 0;
  }
}

bool Lexer::match(char32_t expected) {
  if (peek() == expected) {
    advance();
    return true;
  }
  return false;
}

void Lexer::skip_whitespace() {
  while (const char32_t c = peek()) {
    if (is_whitespace(c)) {
      source_->advance();
      if (c == '\n') ++next_line_;
    } else {
      return;
    }
  }
}

Token Lexer::match_number(char32_t first_char) {
  std::string number;
  if (first_char == '-') {
    number += '-';
    first_char = advance();
  }
  if (first_char == '0') {
    if (match('x') || match('X')) {
      return match_integer(number, is_hex_digit, 16);
    } else if (match('o') || match('O')) {
      return match_integer(number, is_octal_digit, 8);
    } else if (match('b') || match('B')) {
      return match_integer(number, is_binary_digit, 2);
    }
  }
  number += first_char;
  consume_digits(number, is_decimal_digit);

  if (match('.')) {
    return match_fp_from_decimal(number);
  } else if (match('e') || match('E')) {
    return match_fp_from_exponent(number);
  } else if (match('f') || match('F')) {
    return match_fp(number);
  }
  return match_integer(number, is_decimal_digit, 10);
}

template <typename Pred>
void Lexer::consume_digits(std::string& number, Pred is_digit) {
  enum { DIGIT, UNDERSCORE, NONE } state = NONE;
  if (!number.empty()) {
    if (is_digit(number.back())) {
      state = DIGIT;
    } else if (number.back() == '_') {
      state = UNDERSCORE;
    }
  }
  while (!at_end()) {
    char32_t c = peek();
    if (is_digit(c)) {
      state = DIGIT;
      number += static_cast<char>(advance());
    } else if (c == '_') {
      if (state != DIGIT) {
        error("In numeric literal, '_' must follow a digit.");
      }
      state = UNDERSCORE;
      advance();
    } else {
      break;
    }
  }
  if (state == UNDERSCORE) {
    error("Numeric constant may not end with '_'");
  }
}

template <typename Pred>
Token Lexer::match_integer(std::string& number, Pred is_digit, int base) {
  consume_digits(number, is_digit);
  const bool is_int = match('i') || match('I');

  if (!at_end()) {
    char32_t c = peek();
    if (!is_whitespace(c) && !can_start_operator(c)) {
      error(fmt::format("Illegal digit '{}' in literal with base {}",
                        char32_to_string(peek()), base));
    }
  }
  if (is_int) {
    int64_t value;
    const char* last = number.data() + number.size();
    auto result = std::from_chars(number.data(), last, value, base);
    if (result.ec != std::errc{}) {
      if (result.ec == std::errc::result_out_of_range) {
        error(
            "Integer constant could not be represented by a 64-bit signed "
            "integer.");
      }
    }
    if (result.ptr != last) {
      throw std::logic_error("Error parsing integer constant.");
    }
    return make_token(TokenType::ILITERAL, value);
  } else {
    return make_token(TokenType::ILITERAL, mpz_class{number, base});
  }
}

Token Lexer::match_fp_from_decimal(std::string& number) {
  number += '.';
  consume_digits(number, is_decimal_digit);
  if (match('e') || match('E')) {
    return match_fp_from_exponent(number);
  } else {
    match('f') || match('F');
    return match_fp(number);
  }
}

Token Lexer::match_fp_from_exponent(std::string& number) {
  number += 'e';
  int has_digit = false;
  if (match('-')) {
    number += '-';
  } else if (match('+')) {
    number += '+';
  }
  while (!at_end() && is_decimal_digit(peek())) {
    has_digit = true;
    number += advance();
  }
  if (!has_digit) {
    error("Floating point exponent has no digits.");
  }
  return match_fp(number);
}

Token Lexer::match_fp(std::string& number) {
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

Token Lexer::match_char() {
  char32_t value;
  switch (char32_t c = advance_safe("character")) {
    case '"':
      error("Empty character constant.");

    case '\\':
      value = match_escape();
      break;

    default:
      value = c;
  }
  if (!match('"')) {
    error("Multi-character character constant.");
  }
  return make_token(TokenType::CHAR, value);
}

Token Lexer::match_string(StringType type, std::u32string_view raw_delimiter) {
  std::u8string contents;
  auto it = back_inserter(contents);
  while (!match_end_of_string(type, raw_delimiter)) {
    char32_t c = advance_safe("string");
    if (c == '\\' && type != StringType::RAW) {
      if (is_whitespace(peek())) {
        match_gap(type);
      } else {
        utf8::append(match_escape(), it);
      }
    } else {
      if (c == '\n') {
        ++next_line_;
        if (type == StringType::SIMPLE) {
          error(
              "Line breaks are not permitted in strings delimited with a "
              "single "
              "'\"' except in a gap.");
        }
      }
      utf8::append(c, it);
    }
  }
  return make_token(TokenType::STRING, std::move(contents));
}

void Lexer::match_gap(StringType type) {
  if (type != StringType::SIMPLE) {
    error("Gaps only permitted in strings delimited with a single '\"'");
  }
  for (char32_t c = peek(); is_whitespace(c); c = peek()) {
    advance_safe("gap in string");
    if (c == '\n') ++next_line_;
  }
  if (!match('\\')) {
    error("Gap must begin and end with '\\' and contain only whitespace.");
  }
}

std::u32string Lexer::match_raw_delimiter() {
  for (char32_t c = advance_safe("raw string delimiter"); c != '(';
       c = advance_safe("raw string delimiter")) {
    if (c == ')' || c == '\\' || c == 0 || is_whitespace(c)) {
      error(fmt::format("Illegal character '{}' in raw string delimiter",
                        char32_to_string(c)));
    }
  }
  return current_token_.substr(2, current_token_.size() - 3);
}

bool Lexer::match_end_of_string(StringType type,
                                std::u32string_view raw_delimiter) {
  switch (type) {
    case StringType::SIMPLE:
      return match('"');

    case StringType::TRIPLE:
      if (peek() == '"' && peek(1) == '"' && peek(2) == '"') {
        advance();
        advance();
        advance();
        return true;
      }
      return false;

    case StringType::RAW:
      if (peek() == ')') {
        for (std::size_t i = 0; i < raw_delimiter.size(); ++i) {
          if (peek(i + 1) != raw_delimiter[i]) return false;
        }
        if (peek(1 + raw_delimiter.size()) == '"') {
          for (std::size_t i = 0; i < 2 + raw_delimiter.size(); ++i) {
            advance();
          }
          return true;
        }
      }
      return false;
  }
  throw std::logic_error("Illegal value for StringType (match_end_of_string)");
}

char32_t Lexer::match_escape() {
  switch (char32_t c = advance_safe("character escape")) {
    case '"':
    case '\\':
    case '$':
      return c;

    case 'a':
      return '\a';
    case 'b':
      return '\b';
    case 'f':
      return '\f';
    case 'n':
      return '\n';
    case 'r':
      return '\r';
    case 't':
      return '\t';
    case 'v':
      return '\v';
    case '^': {
      char32_t cc = advance_safe("character escape");
      if (cc < 64 || 95 < cc)
        error(
            fmt::format("Illegal escape code '\\^{}'.", char32_to_string(cc)));
      return cc - 64;
    }
    case 'u':
      return match_short_unicode_escape();
    case 'U':
      return match_long_unicode_escape();
    default:
      error(fmt::format("Illegal escape character '{}'", char32_to_string(c)));
  }
}

char32_t Lexer::match_short_unicode_escape() {
  char32_t val = match_hex_digit() << 12;
  val += match_hex_digit() << 8;
  val += match_hex_digit() << 4;
  val += match_hex_digit();
  if (0xD800 <= val && val <= 0xDFFF) {
    error(fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
  }
  return val;
}

char32_t Lexer::match_long_unicode_escape() {
  char32_t val = match_hex_digit() << 20;
  val += match_hex_digit() << 16;
  val += match_hex_digit() << 12;
  val += match_hex_digit() << 8;
  val += match_hex_digit() << 4;
  val += match_hex_digit();
  if ((0xD800 <= val && val <= 0xDFFF) || 0x10FFFF < val) {
    error(fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
  }
  return val;
}

uint_fast8_t Lexer::match_hex_digit() {
  char32_t c = advance_safe("hexadecimal constant");
  if ('0' <= c && c <= '9') {
    return c - '0';
  } else if ('a' <= c && c <= 'f') {
    return 10 + c - 'a';
  } else if ('A' <= c && c <= 'F') {
    return 10 + c - 'A';
  } else {
    error(fmt::format("Illegal hex digit '{}'.", char32_to_string(c)));
  }
}

Token Lexer::match_identifier(char32_t first_char) {
  if (can_start_word(first_char)) return match_id_word(first_char);
  if (can_start_operator(first_char)) return match_id_op(first_char);

  error(fmt::format("Illegal token starting with '{}'",
                    char32_to_string(first_char)));
}

Token Lexer::match_id_word(char32_t first_char) {
  std::u8string identifier;
  auto it = back_inserter(identifier);
  it = utf8::append(first_char, it);
  while (can_continue_word(peek())) {
    utf8::append(advance(), it);
  }
  return make_token(TokenType::ID_WORD, normalize(std::move(identifier)));
}

Token Lexer::match_id_op(char32_t first_char) {
  source_->putback(first_char);
  current_token_.pop_back();
  while (can_start_operator(peek())) {
    next_grapheme_cluster(*source_, current_token_);
  }
  std::u8string identifier;
  utf8::utf32to8(begin(current_token_), end(current_token_),
                 back_inserter(identifier));
  return make_token(TokenType::ID_OP, normalize(std::move(identifier)));
}

bool Lexer::can_start_word(char32_t c) {
  UnicodeError err(*this);

  if (c == '_' || c == '\'') return true;
  if (u_hasBinaryProperty(c, UCHAR_XID_START) &&
      uscript_getUsage(uscript_getScript(c, err)) ==
          USCRIPT_USAGE_RECOMMENDED) {
    return true;
  }
  err.assertSuccess();
  return false;
}

bool Lexer::can_continue_word(char32_t c) {
  UnicodeError err(*this);
  if (can_start_word(c)) return true;
  if (u_hasBinaryProperty(c, UCHAR_XID_CONTINUE) &&
      uscript_getUsage(uscript_getScript(c, err)) ==
          USCRIPT_USAGE_RECOMMENDED) {
    return true;
  }
  err.assertSuccess();
  return false;
}

std::u8string Lexer::normalize(std::u8string&& s) {
  UnicodeError err(*this);
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

}  // namespace emil
