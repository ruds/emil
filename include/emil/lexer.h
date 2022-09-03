#pragma once

#include <cstddef>
#include <cstdint>
#include <exception>
#include <istream>
#include <memory>
#include <string>
#include <string_view>
#include <utility>

#include "emil/source.h"
#include "emil/token.h"
#include "fmt/core.h"

namespace emil {

class LexingError : public std::exception {
 public:
  LexingError(std::string msg, std::string filename, int line,
              std::u32string partial_token_text)
      : msg(std::move(msg)),
        filename(std::move(filename)),
        line(line),
        partial_token_text(partial_token_text),
        full_msg(
            fmt::format("{}:{}: error: {}", this->filename, line, this->msg)) {}

  virtual const char* what() const noexcept override {
    return full_msg.c_str();
  }

  const std::string msg;
  const std::string filename;
  const int line;
  const std::u32string partial_token_text;
  const std::string full_msg;
};

class Lexer {
 public:
  Lexer(std::string filename, std::unique_ptr<Source> source);

  Token next_token();

  /** Advances past the given substring. Used for testing. */
  void advance_past(std::u32string_view substring);

 private:
  const std::string filename_;
  const std::unique_ptr<Source> source_;
  std::u32string current_token_;
  int start_line_ = 1;
  int next_line_ = 1;

  Token make_token(TokenType type, token_auxiliary_t aux = {}) const;
  [[noreturn]] void error(std::string msg);

  char32_t advance();
  char32_t peek(size_t lookahead = 0) const;
  bool match(char32_t expected);

  void skip_whitespace();

  /**
   * Matches a character literal.
   *
   * @invariant current_token_ contains `$=`.
   */
  Token match_char();

  /**
   * Matches a character escape.
   *
   * @invariant current_token_ ends with `\`.
   */
  char32_t match_escape();

  /** Matches and converts a hex digit or throws an error. */
  uint_fast8_t match_hex_digit();
};

}  // namespace emil
