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

#include <algorithm>
#include <initializer_list>
#include <memory>
#include <variant>

#include "emil/ast.h"
#include "emil/token.h"

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
  try {
    switch (t.type) {
      case TokenType::END_OF_FILE:
        return std::make_unique<EndOfFileTopDecl>(t.location);

      case TokenType::SEMICOLON:
        return std::make_unique<EmptyTopDecl>(t.location);

      default: {
        auto decl = std::make_unique<ExprTopDecl>(t.location, match_expr(t));
        consume(TokenType::SEMICOLON, "top-level declaration");
        return decl;
      }
    }
  } catch (ParsingError&) {
    synchronize();
    throw;
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

Token& Parser::advance_safe(std::string_view production) {
  if (at_end()) {
    error(fmt::format("End of file while parsing {}.", production),
          *eof_token_);
  }
  return advance();
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

bool Parser::match(std::initializer_list<TokenType> ts) {
  const Token* next = peek();
  if (next && std::find(begin(ts), end(ts), next->type) != end(ts)) {
    advance();
    return true;
  }
  return false;
}

Token& Parser::consume(std::initializer_list<TokenType> ts,
                       std::string_view production) {
  if (!match(ts)) {
    Token next = ensure_token(peek());
    TokenType next_type = next.type;
    error(fmt::format(
              "While parsing {}, expected token of type {} but instead got {}",
              production, fmt::join(ts, " or "), next_type),
          std::move(next));
  }
  return current_.back();
}

Token Parser::ensure_token(const Token* t) { return t ? *t : *eof_token_; }

void Parser::error(std::string message, Token t) {
  throw ParsingError(std::move(message), t.location);
}

void Parser::synchronize() {
  while (!at_end()) {
    const auto& t = advance();
    switch (t.type) {
      case TokenType::SEMICOLON:
        return;
      default:
        break;
    }
  }
}

ExprPtr Parser::match_expr(Token& first) { return match_atomic_expr(first); }

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

ExprPtr Parser::match_atomic_expr(Token& first) {
  switch (first.type) {
    case TokenType::ILITERAL:
      return match_iliteral(first);

    case TokenType::FPLITERAL:
      return std::make_unique<FpLiteralExpr>(first.location,
                                             get<double>(first.aux));

    case TokenType::STRING:
      return std::make_unique<StringLiteralExpr>(
          first.location, std::move(get<std::u8string>(first.aux)));

    case TokenType::CHAR:
      return std::make_unique<CharLiteralExpr>(first.location,
                                               get<char32_t>(first.aux));

    case TokenType::ID_WORD:
      return match_qual_word_id(first);

    case TokenType::KW_OP: {
      const bool is_prefix_op = match(TokenType::KW_PREFIX);
      Token& t =
          consume({TokenType::ID_WORD, TokenType::ID_OP}, "qualified operator");
      auto expr = match_qual_op_id(t);
      expr->is_prefix_op = is_prefix_op;
      return expr;
    }

    case TokenType::LBRACE:
      return match_record_expr(first.location);

    default:
      error("Bad token to start expression", first);
  }
}

std::unique_ptr<IdentifierExpr> Parser::match_qual_id(Token& first,
                                                      bool allow_word,
                                                      bool allow_op) {
  Token* t = &first;
  std::vector<std::u8string> qualifiers;
  while (t->type == TokenType::ID_WORD && match(TokenType::DOT)) {
    qualifiers.push_back(std::move(get<std::u8string>(t->aux)));
    t = &consume({TokenType::ID_WORD, TokenType::ID_OP},
                 "qualified identifier");
  }
  if (t->type == TokenType::ID_WORD) {
    if (!allow_word) error("Got word identifier when operator expected.", *t);
  } else if (t->type == TokenType::ID_OP) {
    if (!allow_op) error("Got operator identifier when word expected.", *t);
  }
  return std::make_unique<IdentifierExpr>(first.location, std::move(qualifiers),
                                          std::move(get<std::u8string>(t->aux)),
                                          t->type == TokenType::ID_OP);
}

std::unique_ptr<RecordExpr> Parser::match_record_expr(
    const Location& location) {
  std::vector<std::unique_ptr<RecRowSubexpr>> rows;
  if (!match(TokenType::RBRACE)) {
    do {
      rows.push_back(match_rec_row());
    } while (consume({TokenType::RBRACE, TokenType::COMMA}, "record expression")
                 .type == TokenType::COMMA);
  }
  return std::make_unique<RecordExpr>(location, std::move(rows));
}

std::unique_ptr<RecRowSubexpr> Parser::match_rec_row() {
  auto& label = consume(TokenType::ID_WORD, "record expression row");
  const auto& assignment = consume(TokenType::ID_OP, "record expression row");
  const auto& op = get<std::u8string>(assignment.aux);
  if (op != u8"=") {
    error(fmt::format("Expected '=' but got {}", to_std_string(op)),
          assignment);
  }
  auto expr = match_expr(advance_safe("record expression row"));
  return std::make_unique<RecRowSubexpr>(
      label.location, std::move(get<std::u8string>(label.aux)),
      std::move(expr));
}

}  // namespace emil
