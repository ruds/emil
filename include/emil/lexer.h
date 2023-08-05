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

#include <exception>
#include <memory>
#include <string>

#include "emil/processor.h"
#include "emil/token.h"

namespace emil {

struct lexer_impl;

/** Converts a stream of characters to a stream of tokens. */
struct lexer {
  /** The lexer needs the filename for accurate error reporting. */
  explicit lexer(std::string filename);

  ~lexer();

  /** When true, more characters (or an eof indication) are necessary to
   * complete a token. */
  bool requires_more_input() const;

  const std::string& filename() const;

  /**
   * Provide a stream processor to convert characters to tokens.
   *
   * To avoid undefined behavior, ensure that the `lexer` outlives the
   * `processor`.
   *
   * When a `LexingError` is produced instead of a `Token`, or if the
   * stream is reset, the stream will skip input until the next
   * newline or eof.
   */
  processor::processor<char32_t, processor::Expected<Token>> lex();

 private:
  std::unique_ptr<lexer_impl> impl_;
};

/**
 * Provide a stream processor to convert characters to tokens.
 *
 * When a `LexingError` is produced instead of a `Token`, or if the
 * stream is reset, the stream will skip input until the next
 * newline or eof.
 *
 * When it is necessary to access the current status of the lexer (e.g. whether
 * a token is partially constructed), use `lexer::lex` instead.
 */
processor::processor<char32_t, processor::Expected<Token>> lex(
    std::string filename);

/** An error detected during lexing. */
class LexingError : public std::exception {
 public:
  LexingError(std::string msg, const Location& location,
              std::u32string partial_token_text);

  virtual const char* what() const noexcept override {
    return full_msg.c_str();
  }

  const std::string msg;
  const Location location;
  const std::u32string partial_token_text;
  const std::string full_msg;
};

}  // namespace emil
