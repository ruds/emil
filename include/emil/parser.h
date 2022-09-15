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
#include <optional>
#include <string>
#include <utility>

#include "emil/ast.h"
#include "emil/source.h"
#include "emil/token.h"

namespace emil {

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

class Parser {
 public:
  explicit Parser(std::unique_ptr<Source<Token>> source);

  bool at_end() const;

  std::unique_ptr<TopDecl> next();

 private:
  std::unique_ptr<Source<Token>> source_;
  std::optional<Token> eof_token_;
  std::vector<Token> current_;

  Token& advance();
  const Token* peek(std::size_t lookahead = 0);
  bool match(TokenType t);
  Token ensure_token(const Token* t);

  [[noreturn]] void error(std::string message, Token t);

  std::unique_ptr<Expr> match_expr(Token* first);

  std::unique_ptr<Expr> match_atomic_expr(Token* first);
};

}  // namespace emil
