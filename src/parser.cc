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
using DeclPtr = std::unique_ptr<Decl>;

template <typename... Ts>
struct overload : Ts... {
  using Ts::operator()...;
};
template <typename... Ts>
overload(Ts...) -> overload<Ts...>;

bool starts_decl(TokenType t) {
  switch (t) {
    case TokenType::KW_VAL:
    case TokenType::KW_FUN:
    case TokenType::KW_TYPE:
    case TokenType::KW_DATATYPE:
    case TokenType::KW_EXCEPTION:
    case TokenType::KW_LOCAL:
    case TokenType::KW_OPEN:
    case TokenType::KW_INFIX:
    case TokenType::KW_INFIXR:
    case TokenType::KW_NONFIX:
    case TokenType::KW_PREFIX:
      return true;

    default:
      return false;
  }
}

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
        std::unique_ptr<TopDecl> top_decl;
        if (starts_decl(t.type)) {
          top_decl = std::make_unique<DeclTopDecl>(t.location, match_decl(t));
        } else {
          top_decl = std::make_unique<ExprTopDecl>(t.location, match_expr(t));
        }
        consume(TokenType::SEMICOLON, "top-level declaration");
        return top_decl;
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

DeclPtr Parser::match_decl(Token& first) { return match_val_decl(first); }

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

std::u8string&& move_string(Token& t) {
  return std::move(get<std::u8string>(t.aux));
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
      return std::make_unique<StringLiteralExpr>(first.location,
                                                 move_string(first));

    case TokenType::CHAR:
      return std::make_unique<CharLiteralExpr>(first.location,
                                               get<char32_t>(first.aux));

    case TokenType::FSTRING:
      return match_fstring(first);

    case TokenType::ID_WORD:
    case TokenType::QUAL_ID_WORD:
      return match_id(first);

    case TokenType::LBRACE:
      return match_record_expr(first.location);

    case TokenType::LPAREN:
      return match_paren_expr(first.location);

    case TokenType::LBRACKET:
      return match_list_expr(first.location);

    case TokenType::KW_LET:
      return match_let_expr(first.location);

    default:
      error(fmt::format("Expression may not start with {}", first.type), first);
  }
}

std::unique_ptr<FstringLiteralExpr> Parser::match_fstring(Token& first) {
  std::vector<std::u8string> segments;
  std::vector<ExprPtr> substitutions;
  segments.push_back(move_string(first));
  while (match({TokenType::FSTRING_IEXPR_S, TokenType::FSTRING_IVAR})) {
    Token& t = current_.back();
    if (t.type == TokenType::FSTRING_IVAR) {
      substitutions.push_back(std::make_unique<IdentifierExpr>(
          t.location, std::vector<std::u8string>{}, move_string(t), false));
    } else {
      substitutions.push_back(match_expr(advance_safe("fstring substitution")));
      consume(TokenType::FSTRING_IEXPR_F, "fstring substitution");
    }
    Token& cont = consume(TokenType::FSTRING_CONT, "fstring");
    segments.push_back(move_string(cont));
  }
  return std::make_unique<FstringLiteralExpr>(
      first.location, std::move(segments), std::move(substitutions));
}

std::unique_ptr<IdentifierExpr> Parser::match_id(Token& t) {
  switch (t.type) {
    case TokenType::ID_WORD:
    case TokenType::ID_OP:
    case TokenType::EQUALS:
      return std::make_unique<IdentifierExpr>(
          t.location, std::vector<std::u8string>{}, move_string(t),
          t.type != TokenType::ID_WORD);

    case TokenType::QUAL_ID_OP:
    case TokenType::QUAL_ID_WORD: {
      auto& qual = get<QualifiedIdentifier>(t.aux);
      return std::make_unique<IdentifierExpr>(
          t.location, std::move(qual.qualifiers), std::move(qual.id),
          t.type == TokenType::QUAL_ID_OP);
    }

    default:
      error("Expected identifier", t);
  }
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
  consume(TokenType::EQUALS, "record expression row");
  auto expr = match_expr(advance_safe("record expression row"));
  return std::make_unique<RecRowSubexpr>(label.location, move_string(label),
                                         std::move(expr));
}

std::unique_ptr<Expr> Parser::match_paren_expr(const Location& location) {
  if (match(TokenType::RPAREN)) return std::make_unique<UnitExpr>(location);
  if (match(TokenType::KW_PREFIX)) {
    Token& t =
        consume({TokenType::QUAL_ID_OP, TokenType::ID_OP, TokenType::EQUALS},
                "prefix operator");
    auto expr = match_id(t);
    expr->is_prefix_op = true;
    consume(TokenType::RPAREN, "prefix operator");
    return expr;
  }
  Token& first = advance_safe("parenthesized expression");
  if ((first.type == TokenType::QUAL_ID_OP || first.type == TokenType::ID_OP ||
       first.type == TokenType::EQUALS) &&
      match(TokenType::RPAREN)) {
    return match_id(first);
  }
  std::vector<std::unique_ptr<Expr>> exprs;
  exprs.push_back(match_expr(first));
  TokenType sep =
      consume({TokenType::SEMICOLON, TokenType::COMMA, TokenType::RPAREN},
              "parenthesized expression")
          .type;
  std::string production;
  switch (sep) {
    case TokenType::SEMICOLON:
      production = "sequenced expression";
      break;
    case TokenType::COMMA:
      production = "tuple expression";
      break;
    default:
      return std::move(exprs.front());
  }
  do {
    exprs.push_back(match_expr(advance_safe(production)));
  } while (match(sep));
  consume(TokenType::RPAREN, production);
  if (sep == TokenType::SEMICOLON) {
    return std::make_unique<SequencedExpr>(location, std::move(exprs));
  } else {
    return std::make_unique<TupleExpr>(location, std::move(exprs));
  }
}

std::unique_ptr<ListExpr> Parser::match_list_expr(const Location& location) {
  std::vector<std::unique_ptr<Expr>> exprs;
  if (!match(TokenType::RBRACKET)) do {
      exprs.push_back(match_expr(advance_safe("list expression")));
    } while (consume({TokenType::RBRACKET, TokenType::COMMA}, "list expression")
                 .type != TokenType::RBRACKET);
  return std::make_unique<ListExpr>(location, std::move(exprs));
}

std::unique_ptr<ValDecl> Parser::match_val_decl(Token& first) {
  // TODO: lift this check to match_decl
  if (first.type != TokenType::KW_VAL)
    error(fmt::format("Expected 'val' but got token of type {}", first.type),
          first);
  auto& id = consume(TokenType::ID_WORD, "val declaration");
  consume(TokenType::EQUALS, "val declaration");
  auto expr = match_expr(advance_safe("val declaration"));
  return std::make_unique<ValDecl>(first.location, move_string(id),
                                   std::move(expr));
}

std::unique_ptr<LetExpr> Parser::match_let_expr(const Location& location) {
  std::vector<std::unique_ptr<Decl>> decls;
  do {
    decls.push_back(match_decl(advance_safe("let bindings")));
  } while (!match(TokenType::KW_IN));
  std::vector<std::unique_ptr<Expr>> exprs;
  do {
    exprs.push_back(match_expr(advance_safe("let expression")));
  } while (consume({TokenType::SEMICOLON, TokenType::KW_END}, "let expression")
               .type == TokenType::SEMICOLON);
  return std::make_unique<LetExpr>(location, std::move(decls),
                                   std::move(exprs));
}

}  // namespace emil
