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

#include <deque>
#include <exception>
#include <initializer_list>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
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
  std::deque<Token> current_;

  Token& advance();
  Token& advance_safe(std::string_view production);
  const Token* peek(std::size_t lookahead = 0);
  bool match(TokenType t) { return match({t}); }
  bool match(std::initializer_list<TokenType> ts);
  Token& consume(TokenType t, std::string_view production) {
    return consume({t}, production);
  }
  Token& consume(std::initializer_list<TokenType> ts,
                 std::string_view production);
  Token ensure_token(const Token* t);

  [[noreturn]] void error(std::string message, Token t);
  void synchronize();

  std::unique_ptr<Expr> match_expr(Token& first);

  std::unique_ptr<Decl> match_decl(Token& first);

  Token& consume_eq(std::string_view production);

  std::unique_ptr<Expr> match_atomic_expr(Token& first);

  std::unique_ptr<FstringLiteralExpr> match_fstring(Token& first);

  std::unique_ptr<IdentifierExpr> match_qual_word_id(Token& first) {
    return match_qual_id(first, true, false);
  }
  std::unique_ptr<IdentifierExpr> match_qual_op_id(Token& first) {
    return match_qual_id(first, false, true);
  }
  std::unique_ptr<IdentifierExpr> match_qual_id(Token& first,
                                                bool allow_word = true,
                                                bool allow_op = true);

  std::unique_ptr<RecordExpr> match_record_expr(const Location& location);

  std::unique_ptr<RecRowSubexpr> match_rec_row();

  std::unique_ptr<Expr> match_paren_expr(const Location& location);

  std::unique_ptr<ListExpr> match_list_expr(const Location& location);

  std::unique_ptr<LetExpr> match_let_expr(const Location& location);

  std::unique_ptr<ValDecl> match_val_decl(Token& first);
};

}  // namespace emil
