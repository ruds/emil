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

#pragma once

#include <fmt/core.h>

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

namespace emil {

/** An error detected during lexing. */
class LexingError : public std::exception {
 public:
  LexingError(std::string msg, std::string filename, int line,
              std::u32string partial_token_text)
      : msg(std::move(msg)),
        filename(std::move(filename)),
        line(line),
        partial_token_text(std::move(partial_token_text)),
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

/** Converts a stream of characters to a stream of tokens. */
class Lexer {
 public:
  Lexer(std::string filename, std::unique_ptr<Source> source);

  Token next_token();

  /** Advances past the given substring. Used for testing. */
  void advance_past(std::u32string_view substr);

 private:
  friend class UnicodeError;

  const std::string filename_;
  const std::unique_ptr<Source> source_;
  std::u32string current_token_;
  int start_line_ = 1;
  int next_line_ = 1;

  Token make_token(TokenType type, token_auxiliary_t aux = {}) const;
  [[noreturn]] void error(std::string msg);

  bool at_end() const;
  char32_t advance();
  char32_t advance_safe(const char* part_of_speech);
  char32_t peek(size_t lookahead = 0) const;
  bool match(char32_t expected);

  void skip_whitespace();
  void skip_comment();

  /**
   * Matches an integer or floating-point literal.
   *
   * @invariant requires that current_token_ contains `first_char`. If
   * `first_char` is `-`, `peek()` must be a decimal digit.
   */
  Token match_number(char32_t first_char);

  template <typename Pred>
  void consume_digits(std::string& number, Pred is_digit);

  template <typename Pred>
  Token match_integer(std::string& number, Pred is_digit, int base);

  Token match_fp_from_decimal(std::string& number);

  Token match_fp_from_exponent(std::string& number);

  Token match_fp(std::string& number);

  /**
   * Matches a character literal.
   *
   * @invariant requires that current_token_ contains `$=`.
   */
  Token match_char();

  enum class StringType {
    SIMPLE,  // "string"
    TRIPLE,  // """string"""
    RAW,     // r"delim(string)delim"
  };

  /**
   * Matches a string literal.
   *
   * @invariant requires that current_token_ contains the initial
   * delimiter.
   */
  Token match_string(StringType type, std::u32string_view raw_delimiter = U"");

  void match_gap(StringType type);

  std::u32string match_raw_delimiter();

  /**
   * Matches the end of a string literal.
   *
   * Advances the stream if and only if the end of literal matches.
   */
  bool match_end_of_string(StringType type, std::u32string_view raw_delimiter);

  /**
   * Matches a character escape.
   *
   * @invariant requires that current_token_ ends with `\`.
   */
  char32_t match_escape();

  char32_t match_short_unicode_escape();

  char32_t match_long_unicode_escape();

  /** Matches and converts a hex digit or throws an error. */
  uint_fast8_t match_hex_digit();

  Token match_identifier(char32_t first_char);

  Token match_id_word(char32_t first_char);

  Token match_id_op(char32_t first_char);

  bool can_start_word(char32_t c);
  bool can_continue_word(char32_t c);

  std::u8string normalize(std::u8string&& s);
};

}  // namespace emil
