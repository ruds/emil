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

class TopDecl;
struct next_token;

/** Converts a stream of characters to a stream of tokens. */
struct parser {
  ~parser();

  /** When true, more tokens (or an eof indication) are necessary to
   * complete a declaration. */
  bool requires_more_input() const;

  /**
   * Provide a stream processor to convert tokens to ASTs.
   *
   * To avoid undefined behavior, ensure that the `parser` outlives the
   * `processor`.
   *
   * When a `ParsingError` is produced instead of a `TopDecl` or the
   * stream is reset, the stream will discard any AST in progress and
   * start again with the next token.
   */
  processor::processor<Token, processor::Expected<std::unique_ptr<TopDecl>>>
  parse();

 private:
  next_token* next_token_ = nullptr;
};

/**
 * Provide a stream processor to convert tokens to ASTs.
 *
 * To avoid undefined behavior, ensure that the `parser` outlives the
 * `processor`.
 *
 *
 * When a `ParsingError` is produced instead of a `TopDecl` or the
 * stream is reset, the stream will discard any AST in progress and
 * start again with the next token.
 *
 * When it is necessary to access the current state of the parser (e.g. whether
 * an AST node is partially constructed), use `parser::parse` instead.
 */
processor::processor<Token, processor::Expected<std::unique_ptr<TopDecl>>>
parse();

class ParsingError : public std::exception {
 public:
  ParsingError(std::string msg, const Location& location);

  virtual const char* what() const noexcept override {
    return full_msg.c_str();
  }

  const std::string msg;
  const Location location;
  const std::string full_msg;
};

}  // namespace emil
