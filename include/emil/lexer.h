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

class Lexer {
 public:
  Lexer(std::string filename, std::unique_ptr<Source> source);

  Token next_token();

  /** Advances past the given substring. Used for testing. */
  void advance_past(std::u32string_view substr);

 private:
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

  /** Matches and converts a hex digit or throws an error. */
  uint_fast8_t match_hex_digit();
};

}  // namespace emil
