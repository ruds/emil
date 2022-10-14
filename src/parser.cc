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
#include <stdexcept>
#include <string>
#include <variant>

#include "emil/ast.h"
#include "emil/token.h"

namespace emil {

namespace {

using ExprPtr = std::unique_ptr<Expr>;
using DeclPtr = std::unique_ptr<Decl>;
using PatternPtr = std::unique_ptr<Pattern>;
using TypePtr = std::unique_ptr<Type>;

template <typename... Ts>
struct overload : Ts... {
  using Ts::operator()...;
};
template <typename... Ts>
overload(Ts...) -> overload<Ts...>;

#define NON_QUAL_OP_TYPES \
  TokenType::ID_OP, TokenType::EQUALS, TokenType::ASTERISK
#define QUAL_OP_TYPES TokenType::QUAL_ID_OP, NON_QUAL_OP_TYPES

bool is_op(const Token* t, bool allow_qualified) {
  return t && (t->type == TokenType::ID_OP || t->type == TokenType::EQUALS ||
               t->type == TokenType::ASTERISK ||
               (allow_qualified && t->type == TokenType::QUAL_ID_OP));
}

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

std::u8string&& move_string(Token& t) {
  return std::move(get<std::u8string>(t.aux));
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

ExprPtr Parser::match_expr(Token& first) {
  auto expr = match_atomic_expr(first);
  if (match(TokenType::COLON)) {
    auto type = match_type(advance_safe("typed expression"));
    return std::make_unique<TypedExpr>(first.location, std::move(expr),
                                       std::move(type));
  }
  return expr;
}

DeclPtr Parser::match_decl(Token& first) { return match_val_decl(first); }

PatternPtr Parser::match_pattern(Token& first) {
  if (first.type == TokenType::ID_WORD) {
    // match type annotation
    if (match(TokenType::KW_AS)) {
      return std::make_unique<LayeredPattern>(
          first.location, move_string(first),
          match_pattern(advance_safe("layered pattern")));
    }
  }
  auto pattern = match_left_pattern(first);
  // TODO: support infix precendence
  // TODO: support type annotation
  return pattern;
}

TypePtr Parser::match_type(Token& first) {
  auto t = match_tuple_type(first);
  if (match(TokenType::TO_TYPE)) {
    auto ret = match_type(advance_safe("function type"));
    return std::make_unique<FuncType>(first.location, std::move(t),
                                      std::move(ret));
  }
  return t;
}

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
    case TokenType::ASTERISK:
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
    Token& t = consume({QUAL_OP_TYPES}, "prefix operator");
    auto expr = match_id(t);
    expr->is_prefix_op = true;
    consume(TokenType::RPAREN, "prefix operator");
    return expr;
  }
  Token& first = advance_safe("parenthesized expression");
  if (is_op(&first, true) && match(TokenType::RPAREN)) {
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
  std::vector<std::pair<PatternPtr, ExprPtr>> bindings;
  do {
    auto pattern = match_pattern(advance_safe("val declaration"));
    consume(TokenType::EQUALS, "val declaration");
    auto expr = match_expr(advance_safe("val declaration"));
    bindings.emplace_back(std::move(pattern), std::move(expr));
  } while (match(TokenType::KW_AND));
  return std::make_unique<ValDecl>(first.location, std::move(bindings));
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

namespace {
bool can_start_atomic_pattern(const Token* t) {
  if (!t) return false;
  switch (t->type) {
    case TokenType::KW_UNDERSCORE:
    case TokenType::STRING:
    case TokenType::FSTRING:
    case TokenType::ILITERAL:
    case TokenType::ID_WORD:
    case TokenType::QUAL_ID_WORD:
    case TokenType::LBRACE:
    case TokenType::LBRACKET:
    case TokenType::LPAREN:
      return true;

    default:
      return false;
  }
}

std::unique_ptr<IdentifierPattern> make_id_pattern(
    const Location& location, std::vector<std::u8string> qualifiers,
    std::u8string id, bool is_op, bool is_prefix) {
  return std::make_unique<IdentifierPattern>(location, std::move(qualifiers),
                                             std::move(id), is_op, is_prefix);
}

std::unique_ptr<IdentifierPattern> make_id_pattern(Token& t,
                                                   bool is_prefix = false) {
  switch (t.type) {
    case TokenType::QUAL_ID_OP:
    case TokenType::QUAL_ID_WORD: {
      auto& qid = get<QualifiedIdentifier>(t.aux);
      const bool is_op = t.type == TokenType::QUAL_ID_OP;
      return make_id_pattern(t.location, std::move(qid.qualifiers),
                             std::move(qid.id), is_op, is_prefix && is_op);
    }

    case TokenType::ID_OP:
    case TokenType::EQUALS:
    case TokenType::ASTERISK:
      return make_id_pattern(t.location, {}, move_string(t), true, is_prefix);

    case TokenType::ID_WORD:
      return make_id_pattern(t.location, {}, move_string(t), false, false);

    default:
      throw std::logic_error(
          fmt::format("This token shouldn't make it here: {}.", t));
  }
}

}  // namespace

PatternPtr Parser::match_left_pattern(Token& first) {
  auto maybe_id =
      maybe_match_parenthesized_op_pattern(first, AllowQualified::YES);
  if (!maybe_id && (first.type == TokenType::QUAL_ID_WORD ||
                    first.type == TokenType::ID_WORD)) {
    maybe_id = make_id_pattern(first);
  }
  if (maybe_id) {
    if (can_start_atomic_pattern(peek())) {
      auto pattern = match_atomic_pattern(advance());
      return std::make_unique<DatatypePattern>(
          first.location, std::move(maybe_id), std::move(pattern));
    } else if (maybe_id->qualifiers.empty() || !maybe_id->is_op) {
      return maybe_id;
    } else {
      error("Qualified operator not permitted as atomic pattern", first);
    }
  }
  return match_atomic_pattern(first);
}

PatternPtr Parser::match_atomic_pattern(Token& first) {
  auto maybe_op =
      maybe_match_parenthesized_op_pattern(first, AllowQualified::NO);
  if (maybe_op) return maybe_op;

  switch (first.type) {
    case TokenType::KW_UNDERSCORE:
      return std::make_unique<WildcardPattern>(first.location);

    case TokenType::ILITERAL:
    case TokenType::STRING:
    case TokenType::FSTRING:
      return std::make_unique<LiteralPattern>(first.location,
                                              match_atomic_expr(first));

    case TokenType::ID_WORD:
    case TokenType::QUAL_ID_WORD:
      return make_id_pattern(first, false);

    case TokenType::LBRACE:
      return match_record_pattern(first.location);

    case TokenType::LBRACKET:
      return match_list_pattern(first.location);

    case TokenType::LPAREN:
      return match_paren_pattern(first.location);

    default:
      error("Unexpected token when parsing atomic pattern", first);
  }
}

PatternPtr Parser::match_record_pattern(const Location& location) {
  std::vector<std::unique_ptr<Subpattern>> rows;
  if (!match(TokenType::RBRACE)) {
    do {
      if (match(TokenType::ELLIPSIS)) {
        rows.push_back(std::make_unique<RecRowWildcardSubpattern>(
            current_.back().location));
      } else {
        auto& label = consume(TokenType::ID_WORD, "record row pattern");
        PatternPtr pattern;
        if (match(TokenType::EQUALS)) {
          pattern = match_pattern(advance_safe("record row pattern"));
        } else if (match(TokenType::KW_AS)) {
          pattern = std::make_unique<LayeredPattern>(
              label.location, get<std::u8string>(label.aux),
              match_pattern(advance_safe("record row layered pattern")));
        } else {
          pattern = make_id_pattern(
              label.location, {}, get<std::u8string>(label.aux), false, false);
        }
        rows.push_back(std::make_unique<RecRowSubpattern>(
            label.location, move_string(label), std::move(pattern)));
      }
    } while (match(TokenType::COMMA));
    consume(TokenType::RBRACE, "record pattern");
  }
  return std::make_unique<RecordPattern>(location, std::move(rows));
}

PatternPtr Parser::match_list_pattern(const Location& location) {
  std::vector<std::unique_ptr<Pattern>> patterns;
  if (!match(TokenType::RBRACKET)) {
    do {
      patterns.push_back(match_pattern(advance_safe("list pattern")));
    } while (match(TokenType::COMMA));
    consume(TokenType::RBRACKET, "list pattern");
  }
  return std::make_unique<ListPattern>(location, std::move(patterns));
}

PatternPtr Parser::match_paren_pattern(const Location& location) {
  if (match(TokenType::RPAREN)) {
    return std::make_unique<TuplePattern>(location, std::vector<PatternPtr>{});
  }
  if (match(TokenType::KW_PREFIX)) {
    auto& id = consume({NON_QUAL_OP_TYPES}, "prefix op pattern");
    consume(TokenType::RPAREN, "prefix op pattern");
    return make_id_pattern(id, true);
  }
  if (is_op(peek(), false) && peek(1) && peek(1)->type == TokenType::RPAREN) {
    advance();
    auto& id = current_.back();
    advance();
    return make_id_pattern(id, false);
  }
  std::vector<PatternPtr> patterns;
  do {
    patterns.push_back(match_pattern(advance_safe("parenthesized pattern")));
  } while (match(TokenType::COMMA));
  consume(TokenType::RPAREN, "parenthesized pattern");
  if (patterns.size() == 1) {
    return std::move(patterns.front());
  }
  return std::make_unique<TuplePattern>(location, std::move(patterns));
}

std::unique_ptr<IdentifierPattern> Parser::maybe_match_parenthesized_op_pattern(
    Token& first, AllowQualified allow_qualified) {
  if (first.type != TokenType::LPAREN) return nullptr;

  if (match(TokenType::KW_PREFIX)) {
    Token& next = allow_qualified ? consume({QUAL_OP_TYPES}, "prefix op")
                                  : consume({NON_QUAL_OP_TYPES}, "prefix op");
    consume(TokenType::RPAREN, "prefix op");
    return make_id_pattern(next, true);
  }

  if (is_op(peek(), allow_qualified) && peek(1) &&
      peek(1)->type == TokenType::RPAREN) {
    advance();
    Token& id = current_.back();
    advance();
    return make_id_pattern(id, false);
  }

  return nullptr;
}

TypePtr Parser::match_tuple_type(Token& first) {
  std::vector<TypePtr> types;
  types.push_back(match_atomic_type(first));
  while (match(TokenType::ASTERISK)) {
    types.push_back(match_atomic_type(advance_safe("tuple type expression")));
  }
  if (types.size() == 1) {
    return std::move(types.front());
  }
  return std::make_unique<TupleType>(first.location, std::move(types));
}

namespace {

std::unique_ptr<TyconType> make_tycon_type(const Location& location, Token& t,
                                           std::vector<TypePtr> types = {}) {
  if (t.type == TokenType::QUAL_ID_WORD) {
    auto& qid = get<QualifiedIdentifier>(t.aux);
    return std::make_unique<TyconType>(location, std::move(qid.qualifiers),
                                       std::move(qid.id), std::move(types));
  } else {
    return std::make_unique<TyconType>(location, std::vector<std::u8string>{},
                                       move_string(t), std::move(types));
  }
}

std::unique_ptr<TyconType> make_tycon_type(const Location& location, Token& t,
                                           TypePtr param) {
  std::vector<TypePtr> types;
  types.push_back(std::move(param));
  return make_tycon_type(location, t, std::move(types));
}

}  // namespace

TypePtr Parser::match_atomic_type(Token& first) {
  TypePtr type;
  switch (first.type) {
    case TokenType::ID_TYPE:
      type = std::make_unique<VarType>(first.location, move_string(first));
      break;

    case TokenType::LBRACE:
      type = match_record_type(first.location);
      break;

    case TokenType::LPAREN:
      type = match_paren_type(first.location);
      break;

    case TokenType::QUAL_ID_WORD:
    case TokenType::ID_WORD:
      type = make_tycon_type(first.location, first);
      break;

    default:
      error("Unexpected token in type expression", first);
  }
  while (match({TokenType::QUAL_ID_WORD, TokenType::ID_WORD})) {
    type = make_tycon_type(first.location, current_.back(), std::move(type));
  }
  return type;
}

TypePtr Parser::match_record_type(const Location& location) {
  std::vector<std::pair<std::u8string, TypePtr>> rows;
  if (!match(TokenType::RBRACE)) {
    do {
      auto id = consume(TokenType::ID_WORD, "record row type expression");
      consume(TokenType::COLON, "record row type expression");
      auto type = match_type(advance_safe("record row type expression"));
      rows.emplace_back(move_string(id), std::move(type));
    } while (match(TokenType::COMMA));
    consume(TokenType::RBRACE, "record type expression");
  }
  return std::make_unique<RecordType>(location, std::move(rows));
}

TypePtr Parser::match_paren_type(const Location& location) {
  std::vector<TypePtr> types;
  do {
    types.push_back(match_type(advance_safe("parenthesized type expression")));
  } while (match(TokenType::COMMA));
  consume(TokenType::RPAREN, types.size() == 1 ? "parenthesized type expression"
                                               : "type sequence");
  if (types.size() == 1) {
    return std::move(types.front());
  }
  return make_tycon_type(location,
                         consume({TokenType::ID_WORD, TokenType::QUAL_ID_WORD},
                                 "type constructor expression"),
                         std::move(types));
}

}  // namespace emil
