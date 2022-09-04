#include "emil/lexer.h"

#include <fmt/core.h>
#include <unicode/uchar.h>
#include <utf8/cpp17.h>

#include <cstddef>
#include <cstdint>
#include <istream>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "emil/source.h"
#include "emil/token.h"
#include "private/single_pass_search.h"

namespace emil {

namespace {
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

  if (source_->at_end()) return make_token(TokenType::END);

  char32_t c = advance();

  switch (c) {
    case '#':
      if (match('"')) return match_char();
  }

  error(fmt::format("Illegal token starting with '{}'", char32_to_string(c)));
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

char32_t Lexer::advance() {
  current_token_.push_back(source_->advance());
  return current_token_.back();
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
    if (u_hasBinaryProperty(c, UCHAR_PATTERN_WHITE_SPACE)) {
      source_->advance();
      if (c == '\n') ++next_line_;
    } else {
      return;
    }
  }
}

Token Lexer::match_char() {
  char32_t value;
  switch (char32_t c = advance()) {
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

char32_t Lexer::match_escape() {
  switch (char32_t c = advance()) {
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
      char32_t cc = advance();
      if (cc < 64 || 95 < cc)
        error(
            fmt::format("Illegal escape code '\\^{}'.", char32_to_string(cc)));
      return cc - 64;
    }
    case 'u': {
      char32_t val = match_hex_digit() << 12;
      val += match_hex_digit() << 8;
      val += match_hex_digit() << 4;
      val += match_hex_digit();
      if (0xD800 <= val && val <= 0xDFFF) {
        error(
            fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
      }
      return val;
    }
    case 'U': {
      char32_t val = match_hex_digit() << 20;
      val += match_hex_digit() << 16;
      val += match_hex_digit() << 12;
      val += match_hex_digit() << 8;
      val += match_hex_digit() << 4;
      val += match_hex_digit();
      if ((0xD800 <= val && val <= 0xDFFF) || 0x10FFFF < val) {
        error(
            fmt::format("Illegal unicode codepoint {:04X}", (unsigned int)val));
      }
      return val;
    }
    default:
      error(fmt::format("Illegal escape character '{}'", char32_to_string(c)));
  }
}

uint_fast8_t Lexer::match_hex_digit() {
  char32_t c = advance();
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

}  // namespace emil
