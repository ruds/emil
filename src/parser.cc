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

#include "emil/parser.h"

#include <memory>
#include <variant>

#include "emil/ast.h"

namespace emil {

namespace {

using ExprPtr = std::unique_ptr<Expr>;

template <typename... Ts>
struct overload : Ts... {
  using Ts::operator()...;
};
template <typename... Ts>
overload(Ts...) -> overload<Ts...>;

}  // namespace

ParsingError::ParsingError(std::string msg, const Location& location)
    : msg(std::move(msg)),
      location(location),
      full_msg(fmt::format("{}:{}: error: {}", this->location.filename,
                           this->location.line, this->msg)) {}

Parser::Parser(std::unique_ptr<Source<Token>> source)
    : source_(std::move(source)) {}

bool Parser::at_end() const { return source_->at_end(); }

std::unique_ptr<TopDecl> Parser::next() {
  current_.clear();
  Token& t = advance();
  switch (t.type) {
    case TokenType::END_OF_FILE:
      return std::make_unique<EndOfFileTopDecl>(t.location);

    case TokenType::SEMICOLON:
      return std::make_unique<EmptyTopDecl>(t.location);

    default: {
      auto decl = std::make_unique<ExprTopDecl>(t.location, match_expr(&t));
      if (!match(TokenType::SEMICOLON)) {
        Token next = ensure_token(peek());
        TokenType next_type = next.type;
        error(fmt::format("Top-level declaration must be followed by semicolon "
                          "but was followed by: {}",
                          next_type),
              std::move(next));
      }
      return decl;
    }
  }
  error("Unrecognized token", std::move(t));
}

Token& Parser::advance() {
  current_.push_back(source_->advance());
  if (current_.back().type == TokenType::END_OF_FILE) {
    eof_token_ = current_.back();
  }
  return current_.back();
}

const Token* Parser::peek(std::size_t lookahead) {
  const Token* peeked = source_->peek(lookahead);
  if (!peeked && !eof_token_) {
    do {
      --lookahead;
      const Token* p = source_->peek(lookahead);
      if (p) eof_token_ = *p;
    } while (1);
  }
  return peeked;
}

bool Parser::match(TokenType t) {
  const Token* next = peek();
  if (next && next->type == t) {
    advance();
    return true;
  }
  return false;
}

Token Parser::ensure_token(const Token* t) { return t ? *t : *eof_token_; }

void Parser::error(std::string message, Token t) {
  throw ParsingError(std::move(message), t.location);
}

ExprPtr Parser::match_expr(Token* first) { return match_atomic_expr(first); }

namespace {

ExprPtr match_iliteral(Token& t) {
  return visit(overload{[&t](int64_t i) -> ExprPtr {
                          return std::make_unique<IntLiteralExpr>(t.location,
                                                                  i);
                        },
                        [&t](mpz_class& n) -> ExprPtr {
                          return std::make_unique<BigintLiteralExpr>(
                              t.location, std::move(n));
                        },
                        [&t](const auto&) -> ExprPtr {
                          throw std::logic_error("Bad aux type for ILITERAL");
                        }},
               t.aux);
}

}  // namespace

ExprPtr Parser::match_atomic_expr(Token* first) {
  Token& t = first ? *first : advance();
  switch (t.type) {
    case TokenType::ILITERAL:
      return match_iliteral(t);

    case TokenType::FPLITERAL:
      return std::make_unique<FpLiteralExpr>(t.location, get<double>(t.aux));

    case TokenType::STRING:
      return std::make_unique<StringLiteralExpr>(
          t.location, std::move(get<std::u8string>(t.aux)));

    case TokenType::CHAR:
      return std::make_unique<CharLiteralExpr>(t.location,
                                               get<char32_t>(t.aux));

    default:
      throw ParsingError(fmt::format("Bad token to start expression: {}", t),
                         t.location);
  }
}

}  // namespace emil
