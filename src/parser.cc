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

#include <fmt/core.h>
#include <fmt/format.h>

#include <algorithm>
#include <cassert>
#include <coroutine>
#include <cstdint>
#include <exception>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>
#include <variant>

#include "emil/ast.h"
#include "emil/misc.h"
#include "emil/processor.h"
#include "emil/strconvert.h"
#include "emil/token.h"

// IWYU pragma: no_include <__tree>

namespace emil {

namespace {

using ExprPtr = std::unique_ptr<Expr>;
using DeclPtr = std::unique_ptr<Decl>;
using PatternPtr = std::unique_ptr<Pattern>;
using TypeExprPtr = std::unique_ptr<TypeExpr>;

#define NON_QUAL_OP_TYPES \
  TokenType::ID_OP, TokenType::EQUALS, TokenType::ASTERISK
#define QUAL_OP_TYPES TokenType::QUAL_ID_OP, NON_QUAL_OP_TYPES

bool starts_atomic_expr(TokenType t);

bool is_op(const Token* t, bool allow_qualified) {
  return t && (t->type == TokenType::ID_OP || t->type == TokenType::EQUALS ||
               t->type == TokenType::ASTERISK ||
               (allow_qualified && t->type == TokenType::QUAL_ID_OP));
}

bool has_type(const Token* t, TokenType type) { return t && t->type == type; }

[[noreturn]] void error(std::string message, const Location& location) {
  throw ParsingError(std::move(message), location);
}

[[noreturn]] void error(std::string message, const Token& t) {
  error(std::move(message), t.location);
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
  const Token* next = peek();
  if (!next) throw std::logic_error("Tried to read past EOF");
  try {
    if (next->type == TokenType::END_OF_FILE) {
      advance();
      return std::make_unique<EndOfFileTopDecl>(next->location);
    }
    Location location = next->location;
    std::vector<std::unique_ptr<Decl>> decls;
    while (next && starts_decl(next->type)) {
      decls.push_back(match_decl(advance()));
      next = peek();
    }
    if (match(TokenType::SEMICOLON) || !decls.empty()) {
      return std::make_unique<DeclTopDecl>(location, std::move(decls));
    }
    std::vector<std::unique_ptr<ValBind>> it_binding;
    it_binding.push_back(std::make_unique<ValBind>(
        location, make_id_pattern(location, {}, u8"it", false, false),
        match_expr(advance()), false));
    decls.push_back(std::make_unique<ValDecl>(location, std::move(it_binding),
                                              std::vector<std::u8string>{}));
    consume(TokenType::SEMICOLON, "top-level declaration");
    return std::make_unique<DeclTopDecl>(location, std::move(decls));
  } catch (ParsingError&) {
    synchronize();
    throw;
  }
  error("Unrecognized token", std::move(*next));
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
  const Token* next_token = peek();
  if (next_token &&
      std::find(begin(ts), end(ts), next_token->type) != end(ts)) {
    advance();
    return true;
  }
  return false;
}

Token& Parser::consume(std::initializer_list<TokenType> ts,
                       std::string_view production) {
  if (!match(ts)) {
    Token next_token = ensure_token(peek());
    TokenType next_type = next_token.type;
    error(fmt::format(
              "While parsing {}, expected token of type {} but instead got {}",
              production, fmt::join(ts, " or "), next_type),
          std::move(next_token));
  }
  return current_.back();
}

Token Parser::ensure_token(const Token* t) const {
  return t ? *t : *eof_token_;
}

void Parser::synchronize() { source_->sync(); }

ExprPtr Parser::match_expr(Token& first) {
  auto expr = match_left_expr(first);
  if (match(TokenType::COLON)) {
    auto type = match_type(advance_safe("typed expression"));
    return std::make_unique<TypedExpr>(first.location, std::move(expr),
                                       std::move(type));
  }
  return expr;
}

DeclPtr Parser::match_decl(Token& first) {
  switch (first.type) {
    case TokenType::KW_VAL:
      return match_val_decl(first);

    case TokenType::KW_DATATYPE:
      return match_dtype_decl(first);

    default:
      error(fmt::format("Expected decl but got token of type {}", first.type),
            first);
  }
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

}  // namespace

PatternPtr Parser::match_pattern(Token& first) {
  if (first.type == TokenType::ID_WORD) {
    TypeExprPtr type;
    if (match(TokenType::COLON)) {
      type = match_type(advance_safe("typed pattern"));
    }
    if (match(TokenType::KW_AS)) {
      auto pattern = std::make_unique<LayeredPattern>(
          first.location, move_string(first),
          match_pattern(advance_safe("layered pattern")));
      if (type) {
        return std::make_unique<TypedPattern>(
            first.location, std::move(pattern), std::move(type));
      }
      return pattern;
    }
    if (type) {
      return std::make_unique<TypedPattern>(
          first.location, make_id_pattern(first), std::move(type));
    }
  }
  auto pattern = match_left_pattern(first);
  // TODO: support infix precendence
  if (match(TokenType::COLON)) {
    return std::make_unique<TypedPattern>(
        first.location, std::move(pattern),
        match_type(advance_safe("typed pattern")));
  }
  return pattern;
}

TypeExprPtr Parser::match_type(Token& first) {
  auto t = match_tuple_type(first);
  if (match(TokenType::TO_TYPE)) {
    auto ret = match_type(advance_safe("function type"));
    return std::make_unique<FuncTypeExpr>(first.location, std::move(t),
                                          std::move(ret));
  }
  return t;
}

ExprPtr Parser::match_left_expr(Token& first) {
  switch (first.type) {
    case TokenType::KW_IF:
      error("Not implemented", first);

    case TokenType::KW_CASE:
      return match_case_expr(first.location);

    case TokenType::KW_FN:
      return match_fn_expr(first.location);

    default: {
      std::vector<ExprPtr> exprs;
      exprs.push_back(match_atomic_expr(first));
      while (peek() && starts_atomic_expr(peek()->type)) {
        exprs.push_back(match_atomic_expr(advance()));
      }
      if (exprs.size() == 1) {
        // cppcheck-suppress returnStdMoveLocal
        return std::move(exprs.front());
      }
      return std::make_unique<ApplicationExpr>(first.location,
                                               std::move(exprs));
    }
  }
}

namespace {

ExprPtr match_iliteral(Token& t) {
  return visit(overloaded{[&t](int64_t i) -> ExprPtr {
                            return std::make_unique<IntLiteralExpr>(t.location,
                                                                    i);
                          },
                          [&t](BigintLiteralData& d) -> ExprPtr {
                            return std::make_unique<BigintLiteralExpr>(
                                t.location, std::move(d));
                          },
                          [](const auto&) -> ExprPtr {
                            throw std::logic_error("Bad aux type for ILITERAL");
                          }},
               t.aux);
}

bool starts_atomic_expr(TokenType t) {
  return (t == TokenType::ILITERAL || t == TokenType::FPLITERAL ||
          t == TokenType::STRING || t == TokenType::CHAR ||
          t == TokenType::FSTRING || t == TokenType::ID_WORD ||
          t == TokenType::QUAL_ID_WORD || t == TokenType::LBRACE ||
          t == TokenType::LPAREN || t == TokenType::LBRACKET ||
          t == TokenType::KW_LET);
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

std::unique_ptr<CaseExpr> Parser::match_case_expr(const Location& location) {
  auto expr = match_expr(advance_safe("case expression"));
  consume(TokenType::KW_OF, "case expression");
  return std::make_unique<CaseExpr>(location, std::move(expr), match_cases());
}

std::unique_ptr<FnExpr> Parser::match_fn_expr(const Location& location) {
  return std::make_unique<FnExpr>(location, match_cases());
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

std::unique_ptr<IdentifierExpr> Parser::match_id(Token& first) {
  switch (first.type) {
    case TokenType::ID_WORD:
    case TokenType::ID_OP:
    case TokenType::EQUALS:
    case TokenType::ASTERISK:
      return std::make_unique<IdentifierExpr>(
          first.location, std::vector<std::u8string>{}, move_string(first),
          first.type != TokenType::ID_WORD);

    case TokenType::QUAL_ID_OP:
    case TokenType::QUAL_ID_WORD: {
      auto& qual = get<QualifiedIdentifier>(first.aux);
      return std::make_unique<IdentifierExpr>(
          first.location, std::move(qual.qualifiers), std::move(qual.id),
          first.type == TokenType::QUAL_ID_OP);
    }

    default:
      error("Expected identifier", first);
  }
}

std::unique_ptr<RecordExpr> Parser::match_record_expr(
    const Location& location) {
  std::vector<std::unique_ptr<RecRowExpr>> rows;
  std::set<std::u8string> labels;
  if (!match(TokenType::RBRACE)) {
    do {
      rows.push_back(match_rec_row());
      auto ins_res = labels.insert(rows.back()->label);
      if (!ins_res.second)
        error(fmt::format("Label '{}' bound twice in record expression",
                          to_std_string(rows.back()->label)),
              current_.back());
    } while (consume({TokenType::RBRACE, TokenType::COMMA}, "record expression")
                 .type == TokenType::COMMA);
  }
  return std::make_unique<RecordExpr>(location, std::move(rows));
}

std::unique_ptr<RecRowExpr> Parser::match_rec_row() {
  auto& label = consume(TokenType::ID_WORD, "record expression row");
  consume(TokenType::EQUALS, "record expression row");
  auto expr = match_expr(advance_safe("record expression row"));
  return std::make_unique<RecRowExpr>(label.location, move_string(label),
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
  if (!match(TokenType::RBRACKET)) {
    do {
      exprs.push_back(match_expr(advance_safe("list expression")));
    } while (consume({TokenType::RBRACKET, TokenType::COMMA}, "list expression")
                 .type != TokenType::RBRACKET);
  }
  return std::make_unique<ListExpr>(location, std::move(exprs));
}

std::vector<std::pair<PatternPtr, ExprPtr>> Parser::match_cases() {
  std::vector<std::pair<PatternPtr, ExprPtr>> cases;
  do {
    auto pattern = match_pattern(advance_safe("match expression"));
    consume(TokenType::TO_EXPR, "match expression");
    auto expr = match_expr(advance_safe("match expression"));
    cases.emplace_back(std::move(pattern), std::move(expr));
  } while (match(TokenType::PIPE));
  return cases;
}

std::unique_ptr<ValDecl> Parser::match_val_decl(Token& first) {
  auto explicit_type_vars = match_type_id_seq();
  std::sort(explicit_type_vars.begin(), explicit_type_vars.end());
  std::vector<std::unique_ptr<ValBind>> bindings;
  bool is_recursive = false;
  do {
    bindings.push_back(match_val_bind(advance_safe("val-bind"), is_recursive));
    is_recursive = is_recursive || bindings.back()->rec;
  } while (match(TokenType::KW_AND));
  return std::make_unique<ValDecl>(first.location, std::move(bindings),
                                   std::move(explicit_type_vars));
}

namespace {

void check_no_doublebind(
    const std::vector<std::unique_ptr<DtypeBind>>& bindings) {
  std::set<std::u8string> types;
  std::set<std::u8string> constructors;
  for (const auto& b : bindings) {
    if (!types.insert(b->identifier).second) {
      throw ParsingError(
          fmt::format("bound {} multiple times", to_std_string(b->identifier)),
          b->location);
    }
    for (const auto& c : b->constructors) {
      auto id = canonicalize_val_id(c->identifier, c->is_op, c->is_prefix_op);
      if (!constructors.insert(id).second) {
        throw ParsingError(
            fmt::format("bound {} multiple times", to_std_string(id)),
            c->location);
      }
    }
  }
}

}  // namespace

std::unique_ptr<DtypeDecl> Parser::match_dtype_decl(Token& first) {
  std::vector<std::unique_ptr<DtypeBind>> bindings;
  do {
    bindings.push_back(match_dtype_bind());
  } while (match(TokenType::KW_AND));
  check_no_doublebind(bindings);
  return std::make_unique<DtypeDecl>(first.location, std::move(bindings));
}

std::vector<std::u8string> Parser::match_type_id_seq() {
  std::vector<std::u8string> types;
  if (match(TokenType::ID_TYPE)) {
    types.push_back(move_string(current_.back()));
  } else if (peek() && peek()->type == TokenType::LPAREN && peek(1) &&
             peek(1)->type == TokenType::ID_TYPE) {
    std::set<std::u8string> types_deduped;
    advance();
    do {
      auto s = move_string(consume(TokenType::ID_TYPE, "type id sequence"));
      types.push_back(s);
      if (!types_deduped.insert(s).second) {
        error("type id sequence contains duplicate type ids", current_.back());
      }
    } while (match(TokenType::COMMA));
    if (types.size() == 1) {
      error("Illegal type id sequence with single type id in parentheses",
            current_.back());
    }
    consume(TokenType::RPAREN, "type id sequence");
  }
  return types;
}

std::unique_ptr<ValBind> Parser::match_val_bind(Token& first,
                                                bool is_recursive) {
  const bool rec = first.type == TokenType::KW_REC;
  auto& token = rec ? advance_safe("valbind declaration") : first;
  auto pattern = match_pattern(token);
  consume(TokenType::EQUALS, "valbind declaration");
  ExprPtr expr;
  if (rec || is_recursive) {
    consume(TokenType::KW_FN, "recursive valbind declaration");
    expr = match_fn_expr(current_.back().location);
  } else {
    expr = match_expr(advance_safe("valbind declaration"));
  }
  return std::make_unique<ValBind>(first.location, std::move(pattern),
                                   std::move(expr), rec);
}

namespace {

class TypeVarExtractor : public TypeExpr::Visitor {
 public:
  std::set<std::u8string> vars;

  void visitVarTypeExpr(const VarTypeExpr& e) override { vars.insert(e.id); }

  void visitRecordTypeExpr(const RecordTypeExpr& e) override {
    for (const auto& row : e.rows) {
      row.second->accept(*this);
    }
  }

  void visitTyconTypeExpr(const TyconTypeExpr& e) override {
    for (const auto& t : e.types) {
      t->accept(*this);
    }
  }

  void visitTupleTypeExpr(const TupleTypeExpr& e) override {
    for (const auto& t : e.types) {
      t->accept(*this);
    }
  }

  void visitFuncTypeExpr(const FuncTypeExpr& e) override {
    e.param->accept(*this);
    e.ret->accept(*this);
  }
};

/** Check that any tyvar used in a constructor occurs in `vars`. */
void check_type_vars(
    const Location& location, const std::vector<std::u8string>& vars,
    const std::vector<std::unique_ptr<ConBind>>& constructors) {
  TypeVarExtractor v;

  for (const auto& con : constructors) {
    if (con->param) con->param->accept(v);
  }

  std::set<std::u8string> sorted_vars(vars.begin(), vars.end());
  std::vector<std::u8string> extras;
  std::set_difference(v.vars.begin(), v.vars.end(), sorted_vars.begin(),
                      sorted_vars.end(), back_inserter(extras));
  if (!extras.empty()) {
    std::string outvars;
    for (auto it = extras.begin(); it != extras.end(); ++it) {
      if (it != extras.begin()) outvars += ", ";
      outvars += to_std_string(*it);
    }
    throw ParsingError(
        fmt::format("unbound type variable(s) in type declaration: {}",
                    outvars),
        location);
  }
}

const std::vector<std::u8string_view> RESERVED_NAMES_DATBIND = {
    u8"(::)", u8"false", u8"it", u8"nil", u8"ref", u8"true",
};

/** Check that none of the reserved names are bound. */
void check_names(const Location& location, std::u8string_view type_name,
                 const std::vector<std::unique_ptr<ConBind>>& constructors) {
  assert(std::is_sorted(RESERVED_NAMES_DATBIND.begin(),
                        RESERVED_NAMES_DATBIND.end()));
  if (std::binary_search(RESERVED_NAMES_DATBIND.begin(),
                         RESERVED_NAMES_DATBIND.end(), type_name)) {
    throw ParsingError(fmt::format("Illegally bound {} as datatype name",
                                   to_std_string(type_name)),
                       location);
  }
  for (const auto& c : constructors) {
    const auto id =
        canonicalize_val_id(c->identifier, c->is_op, c->is_prefix_op);
    if (std::binary_search(RESERVED_NAMES_DATBIND.begin(),
                           RESERVED_NAMES_DATBIND.end(), id)) {
      throw ParsingError(fmt::format("Illegal bound {} as value constructor",
                                     to_std_string(id)),
                         location);
    }
  }
}

}  // namespace

std::unique_ptr<DtypeBind> Parser::match_dtype_bind() {
  if (!peek()) {
    error("Expected dtype-bind", current_.back());
  }

  const auto& location = peek()->location;
  auto types = match_type_id_seq();
  auto id = consume(TokenType::ID_WORD, "dtype-bind");
  consume(TokenType::EQUALS, "dtype-bind");
  std::vector<std::unique_ptr<ConBind>> constructors;
  do {
    constructors.push_back(match_con_bind(advance_safe("con-bind")));
  } while (match(TokenType::PIPE));
  check_type_vars(location, types, constructors);
  auto type_name = move_string(id);
  check_names(location, type_name, constructors);
  return std::make_unique<DtypeBind>(location, std::move(type_name),
                                     std::move(types), std::move(constructors));
}

std::unique_ptr<ConBind> Parser::match_con_bind(Token& first) {
  switch (first.type) {
    case TokenType::ID_WORD: {
      // This could be a type expression: foo list list list list list ....
      std::size_t lookahead = 0;
      while (peek(lookahead) && peek(lookahead)->type == TokenType::ID_WORD) {
        ++lookahead;
      }
      if (peek(lookahead)->type == TokenType::ID_OP) {
        return match_infix_con_bind(first);
      }
      std::unique_ptr<TypeExpr> param;
      if (match(TokenType::KW_OF)) {
        param = match_type(advance_safe("con-bind type expression"));
      }
      return std::make_unique<ConBind>(first.location, move_string(first),
                                       std::move(param), false, false);
    }

    case TokenType::ID_OP: {
      std::unique_ptr<TypeExpr> param =
          match_type(advance_safe("con-bind prefix op type"));
      return std::make_unique<ConBind>(first.location, move_string(first),
                                       std::move(param), true, true);
    }

    case TokenType::LPAREN: {
      bool prefix = match(TokenType::KW_PREFIX);
      if (prefix || (peek() && peek()->type == TokenType::ID_OP)) {
        auto id = consume(TokenType::ID_OP, "con-bind paren op");
        consume(TokenType::RPAREN, "con-bind paren op");
        std::unique_ptr<TypeExpr> param;
        if (match(TokenType::KW_OF)) {
          param = match_type(advance_safe("con-bind paren op type"));
        }
        return std::make_unique<ConBind>(first.location, move_string(id),
                                         std::move(param), true, prefix);
      } else {
        return match_infix_con_bind(first);
      }
    }

    default:
      return match_infix_con_bind(first);
  }
}

std::unique_ptr<ConBind> Parser::match_infix_con_bind(Token& first) {
  std::vector<std::unique_ptr<TypeExpr>> types;
  types.push_back(match_type(first));
  auto id = consume(TokenType::ID_OP, "con-bind infix op");
  types.push_back(match_type(advance_safe("con-bind infix op type")));
  return std::make_unique<ConBind>(
      first.location, move_string(id),
      std::make_unique<TupleTypeExpr>(first.location, std::move(types)), true,
      false);
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
  std::vector<std::unique_ptr<RecRowPattern>> rows;
  std::set<std::u8string> labels;
  bool has_wildcard = false;
  if (!match(TokenType::RBRACE)) {
    do {
      if (match(TokenType::ELLIPSIS)) {
        if (has_wildcard)
          error("'...' may not appear twice in a single pattern.",
                current_.back());
        else
          has_wildcard = true;
      } else {
        auto& label = consume(TokenType::ID_WORD, "record row pattern");
        std::u8string label_name = get<std::u8string>(label.aux);
        PatternPtr pattern;
        if (match(TokenType::EQUALS)) {
          pattern = match_pattern(advance_safe("record row pattern"));
        } else {
          TypeExprPtr type;
          if (match(TokenType::COLON)) {
            type = match_type(advance_safe("record row label type expression"));
          }
          if (match(TokenType::KW_AS)) {
            pattern = std::make_unique<LayeredPattern>(
                label.location, label_name,
                match_pattern(advance_safe("record row layered pattern")));
            if (type)
              pattern = std::make_unique<TypedPattern>(
                  label.location, std::move(pattern), std::move(type));
          } else {
            pattern =
                make_id_pattern(label.location, {}, label_name, false, false);
            if (type) {
              pattern = std::make_unique<TypedPattern>(
                  label.location, std::move(pattern), std::move(type));
            }
          }
        }
        auto insres = labels.insert(label_name);
        if (!insres.second) {
          error(fmt::format("Label '{}' was specified twice in pattern",
                            to_std_string(label_name)),
                label);
        }
        rows.push_back(std::make_unique<RecRowPattern>(
            label.location, move_string(label), std::move(pattern)));
      }
    } while (match(TokenType::COMMA));
    consume(TokenType::RBRACE, "record pattern");
  }
  return std::make_unique<RecordPattern>(location, std::move(rows),
                                         has_wildcard);
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
    // cppcheck-suppress returnStdMoveLocal
    return std::move(patterns.front());
  }
  return std::make_unique<TuplePattern>(location, std::move(patterns));
}

std::unique_ptr<IdentifierPattern> Parser::maybe_match_parenthesized_op_pattern(
    const Token& first, AllowQualified allow_qualified) {
  if (first.type != TokenType::LPAREN) return nullptr;

  if (match(TokenType::KW_PREFIX)) {
    Token& next_token = allow_qualified
                            ? consume({QUAL_OP_TYPES}, "prefix op")
                            : consume({NON_QUAL_OP_TYPES}, "prefix op");
    consume(TokenType::RPAREN, "prefix op");
    return make_id_pattern(next_token, true);
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

TypeExprPtr Parser::match_tuple_type(Token& first) {
  std::vector<TypeExprPtr> types;
  types.push_back(match_atomic_type(first));
  while (match(TokenType::ASTERISK)) {
    types.push_back(match_atomic_type(advance_safe("tuple type expression")));
  }
  if (types.size() == 1) {
    // cppcheck-suppress returnStdMoveLocal
    return std::move(types.front());
  }
  return std::make_unique<TupleTypeExpr>(first.location, std::move(types));
}

namespace {

std::unique_ptr<TyconTypeExpr> make_tycon_type(
    const Location& location, Token& t, std::vector<TypeExprPtr> types = {}) {
  if (t.type == TokenType::QUAL_ID_WORD) {
    auto& qid = get<QualifiedIdentifier>(t.aux);
    return std::make_unique<TyconTypeExpr>(location, std::move(qid.qualifiers),
                                           std::move(qid.id), std::move(types));
  } else {
    return std::make_unique<TyconTypeExpr>(location,
                                           std::vector<std::u8string>{},
                                           move_string(t), std::move(types));
  }
}

std::unique_ptr<TyconTypeExpr> make_tycon_type(const Location& location,
                                               Token& t, TypeExprPtr param) {
  std::vector<TypeExprPtr> types;
  types.push_back(std::move(param));
  return make_tycon_type(location, t, std::move(types));
}

}  // namespace

TypeExprPtr Parser::match_atomic_type(Token& first) {
  TypeExprPtr type;
  switch (first.type) {
    case TokenType::ID_TYPE:
      type = std::make_unique<VarTypeExpr>(first.location, move_string(first));
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

TypeExprPtr Parser::match_record_type(const Location& location) {
  std::vector<std::pair<std::u8string, TypeExprPtr>> rows;
  std::set<std::u8string> labels;
  if (!match(TokenType::RBRACE)) {
    do {
      auto id = consume(TokenType::ID_WORD, "record row type expression");
      consume(TokenType::COLON, "record row type expression");
      auto type = match_type(advance_safe("record row type expression"));
      rows.emplace_back(move_string(id), std::move(type));
      auto insres = labels.insert(rows.back().first);
      if (!insres.second) {
        error(fmt::format("Label '{}' bound twice in record type experession.",
                          to_std_string(rows.back().first)),
              id);
      }
    } while (match(TokenType::COMMA));
    consume(TokenType::RBRACE, "record type expression");
  }
  return std::make_unique<RecordTypeExpr>(location, std::move(rows));
}

TypeExprPtr Parser::match_paren_type(const Location& location) {
  std::vector<TypeExprPtr> types;
  do {
    types.push_back(match_type(advance_safe("parenthesized type expression")));
  } while (match(TokenType::COMMA));
  consume(TokenType::RPAREN, types.size() == 1 ? "parenthesized type expression"
                                               : "type sequence");
  if (types.size() == 1) {
    // cppcheck-suppress returnStdMoveLocal
    return std::move(types.front());
  }
  return make_tycon_type(location,
                         consume({TokenType::ID_WORD, TokenType::QUAL_ID_WORD},
                                 "type constructor expression"),
                         std::move(types));
}

namespace {

using processor::eof;
using processor::Expected;
using processor::next_input;
using processor::reset;
using processor::subtask;

using TopDeclPtr = std::unique_ptr<TopDecl>;
using TokenRef = std::reference_wrapper<Token>;

}  // namespace

struct next_token {
  std::deque<Token> tokens;
  std::optional<Token> eof_token;

  subtask<Token, TopDeclPtr> operator()() {
    // If we start off with no tokens available, eof_token won't be set,
    // so we skip the extra machinery of next_token::peek.
    const Token* next = co_await processor::peek{};
    if (!next) {
      throw eof{};
    }

    if (next->type == TokenType::END_OF_FILE) {
      const Token& t = co_await advance();
      co_return std::make_unique<EndOfFileTopDecl>(t.location);
    }

    Location location = next->location;
    std::vector<std::unique_ptr<Decl>> decls;

    while (next && starts_decl(next->type)) {
      decls.push_back(co_await consume_decl());
      next = co_await peek();
    }
    if (co_await match(TokenType::SEMICOLON) || !decls.empty()) {
      co_return std::make_unique<DeclTopDecl>(location, std::move(decls));
    }

    std::vector<std::unique_ptr<ValBind>> it_binding;
    it_binding.push_back(std::make_unique<ValBind>(
        location, make_id_pattern(location, {}, u8"it", false, false),
        co_await consume_expr(), false));
    decls.push_back(std::make_unique<ValDecl>(location, std::move(it_binding),
                                              std::vector<std::u8string>{}));
    co_await consume(TokenType::SEMICOLON, "top-level declaration");
    co_return std::make_unique<DeclTopDecl>(location, std::move(decls));
  }

 private:
  subtask<Token, TokenRef> advance() {
    tokens.push_back(co_await next_input{});
    if (!eof_token && tokens.back().type == TokenType::END_OF_FILE) {
      eof_token = tokens.back();
    }
    co_return tokens.back();
  }

  subtask<Token, TokenRef> advance_safe(std::string_view production) {
    if (!co_await peek()) {
      assert(eof_token);
      error(fmt::format("End of file while parsing {}.", production),
            *eof_token);
    }
    co_return co_await advance();
  }

  subtask<Token, const Token*> peek(std::size_t i = 1) {
    const Token* const peeked = co_await processor::peek{i};
    while (!peeked && !eof_token) {
      --i;
      assert(i);
      const Token* const p = co_await processor::peek{i};
      if (p) eof_token = *p;
    }
    co_return peeked;
  }

  subtask<Token, bool> match(std::initializer_list<TokenType> ts) {
    const Token* const next_token = co_await peek();
    if (next_token &&
        std::find(begin(ts), end(ts), next_token->type) != end(ts)) {
      co_await advance();
      co_return true;
    }
    co_return false;
  }

  subtask<Token, bool> match(TokenType t) { co_return co_await match({t}); }

  Token ensure_token(const Token* t) const { return t ? *t : *eof_token; }

  subtask<Token, TokenRef> consume(std::initializer_list<TokenType> ts,
                                   std::string_view production) {
    if (!co_await match(ts)) {
      Token next_token = ensure_token(co_await peek());
      const TokenType next_type = next_token.type;
      error(
          fmt::format(
              "While parsing {}, expected token of type {} but instead got {}",
              production, fmt::join(ts, " or "), next_type),
          std::move(next_token));
    }
    co_return tokens.back();
  }

  subtask<Token, TokenRef> consume(TokenType t, std::string_view production) {
    co_return co_await consume({t}, production);
  }

  subtask<Token, ExprPtr> consume_expr() {
    auto expr = co_await consume_left_expr();
    if (co_await match(TokenType::COLON)) {
      co_return std::make_unique<TypedExpr>(expr->location, std::move(expr),
                                            co_await consume_type());
    }
    co_return expr;
  }

  subtask<Token, ExprPtr> consume_left_expr() {
    const Token* first = co_await peek();
    switch (first->type) {
      case TokenType::KW_IF:
        error("Not implemented", *first);

      case TokenType::KW_CASE:
        co_return co_await consume_case_expr();

      case TokenType::KW_FN:
        co_return co_await consume_fn_expr();

      default: {
        std::vector<ExprPtr> exprs;
        while (first && starts_atomic_expr(first->type)) {
          exprs.push_back(co_await consume_atomic_expr());
          first = co_await peek();
        }
        if (exprs.empty()) {
          Token& t = co_await advance();
          error(fmt::format("Expected an expression but found token of type {}",
                            t.type),
                t);
        }
        if (exprs.size() == 1) {
          co_return std::move(exprs.front());
        }
        const Location& location = exprs.front()->location;
        co_return std::make_unique<ApplicationExpr>(location, std::move(exprs));
      }
    }
  }

  subtask<Token, ExprPtr> consume_atomic_expr() {
    const Token* const first = co_await peek();

    switch (first->type) {
      case TokenType::ILITERAL:
        co_return match_iliteral(co_await advance());

      case TokenType::FPLITERAL: {
        Token& t = co_await advance();
        co_return std::make_unique<FpLiteralExpr>(t.location,
                                                  get<double>(t.aux));
      }

      case TokenType::STRING: {
        Token& t = co_await advance();
        co_return std::make_unique<StringLiteralExpr>(t.location,
                                                      move_string(t));
      }

      case TokenType::CHAR: {
        Token& t = co_await advance();
        co_return std::make_unique<CharLiteralExpr>(t.location,
                                                    get<char32_t>(t.aux));
      }

      case TokenType::FSTRING:
        co_return co_await consume_fstring();

      case TokenType::ID_WORD:
      case TokenType::QUAL_ID_WORD:
        co_return co_await consume_id();

      case TokenType::LBRACE:
        co_return co_await consume_record_expr();

      case TokenType::LPAREN:
        co_return co_await consume_paren_expr();

      case TokenType::LBRACKET:
        co_return co_await consume_list_expr();

      case TokenType::KW_LET:
        co_return co_await consume_let_expr();

      default: {
        Token& t = co_await advance();
        error(fmt::format("Expression may not start with {}", t.type), t);
      }
    }
  }

  subtask<Token, ExprPtr> consume_fstring() {
    Token& first = co_await consume(TokenType::FSTRING, "fstring");
    std::vector<std::u8string> segments;
    std::vector<ExprPtr> substitutions;
    segments.push_back(move_string(first));

    while (
        co_await match({TokenType::FSTRING_IEXPR_S, TokenType::FSTRING_IVAR})) {
      Token& t = tokens.back();
      if (t.type == TokenType::FSTRING_IVAR) {
        substitutions.push_back(std::make_unique<IdentifierExpr>(
            t.location, std::vector<std::u8string>{}, move_string(t), false));
      } else {
        substitutions.push_back(co_await consume_expr());
        co_await consume(TokenType::FSTRING_IEXPR_F, "fstring substitution");
      }
      Token& cont = co_await consume(TokenType::FSTRING_CONT, "fstring");
      segments.push_back(move_string(cont));
    }
    co_return std::make_unique<FstringLiteralExpr>(
        first.location, std::move(segments), std::move(substitutions));
  }

  subtask<Token, std::unique_ptr<IdentifierExpr>> consume_id() {
    co_return parse_id_token(co_await advance_safe("identifier"));
  }

  std::unique_ptr<IdentifierExpr> parse_id_token(Token& t) {
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

  subtask<Token, ExprPtr> consume_record_expr() {
    Token& first = co_await consume(TokenType::LBRACE, "record expression");
    std::vector<std::unique_ptr<RecRowExpr>> rows;
    std::set<std::u8string> labels;
    if (!co_await match(TokenType::RBRACE)) {
      do {
        rows.push_back(co_await consume_rec_row());
        auto ins_res = labels.insert(rows.back()->label);
        if (!ins_res.second)
          error(fmt::format("Label '{}' bound twice in record expression",
                            to_std_string(rows.back()->label)),
                tokens.back());
      } while ((co_await consume({TokenType::RBRACE, TokenType::COMMA},
                                 "record expression"))
                   .get()
                   .type == TokenType::COMMA);
    }
    co_return std::make_unique<RecordExpr>(first.location, std::move(rows));
  }

  subtask<Token, std::unique_ptr<RecRowExpr>> consume_rec_row() {
    Token& label =
        co_await consume(TokenType::ID_WORD, "record expression row");
    co_await consume(TokenType::EQUALS, "record expression row");
    co_return std::make_unique<RecRowExpr>(label.location, move_string(label),
                                           co_await consume_expr());
  }

  subtask<Token, ExprPtr> consume_paren_expr() {
    const Location& location =
        (co_await consume(TokenType::LPAREN, "parenthesized expression"))
            .get()
            .location;
    if (co_await match(TokenType::RPAREN)) {
      co_return std::make_unique<UnitExpr>(location);
    }
    if (co_await match(TokenType::KW_PREFIX)) {
      Token& t = co_await consume({QUAL_OP_TYPES}, "prefix operator");
      auto expr = parse_id_token(t);
      expr->is_prefix_op = true;
      co_await consume(TokenType::RPAREN, "prefix operator");
      co_return expr;
    }
    if (is_op(co_await peek(), true) &&
        has_type(co_await peek(2), TokenType::RPAREN)) {
      auto expr = co_await consume_id();
      co_await advance();
      co_return expr;
    }

    std::vector<ExprPtr> exprs;
    exprs.push_back(co_await consume_expr());
    TokenType sep = (co_await consume({TokenType::SEMICOLON, TokenType::COMMA,
                                       TokenType::RPAREN},
                                      "parenthesized expression"))
                        .get()
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
        co_return std::move(exprs.front());
    }
    do {
      exprs.push_back(co_await consume_expr());
    } while (co_await match(sep));
    co_await consume(TokenType::RPAREN, production);
    if (sep == TokenType::SEMICOLON) {
      co_return std::make_unique<SequencedExpr>(location, std::move(exprs));
    } else {
      co_return std::make_unique<TupleExpr>(location, std::move(exprs));
    }
  }

  subtask<Token, ExprPtr> consume_list_expr() {
    const Location& location =
        (co_await consume(TokenType::LBRACKET, "list expression"))
            .get()
            .location;
    std::vector<ExprPtr> exprs;
    if (!co_await match(TokenType::RBRACKET)) {
      do {
        exprs.push_back(co_await consume_expr());
      } while ((co_await consume({TokenType::RBRACKET, TokenType::COMMA},
                                 "list expression"))
                   .get()
                   .type != TokenType::RBRACKET);
    }
    co_return std::make_unique<ListExpr>(location, std::move(exprs));
  }

  subtask<Token, ExprPtr> consume_let_expr() {
    const Location& location =
        (co_await consume(TokenType::KW_LET, "let expression")).get().location;
    std::vector<DeclPtr> decls;
    do {
      decls.push_back(co_await consume_decl());
    } while (!co_await match(TokenType::KW_IN));
    std::vector<ExprPtr> exprs;
    do {
      exprs.push_back(co_await consume_expr());
    } while ((co_await consume({TokenType::SEMICOLON, TokenType::KW_END},
                               "let expresion"))
                 .get()
                 .type == TokenType::SEMICOLON);
    co_return std::make_unique<LetExpr>(location, std::move(decls),
                                        std::move(exprs));
  }

  subtask<Token, std::unique_ptr<CaseExpr>> consume_case_expr() {
    Token& first = co_await consume(TokenType::KW_CASE, "case expression");
    auto expr = co_await consume_expr();
    co_await consume(TokenType::KW_OF, "case expression");
    co_return std::make_unique<CaseExpr>(first.location, std::move(expr),
                                         co_await consume_cases());
  }

  subtask<Token, std::vector<std::pair<PatternPtr, ExprPtr>>> consume_cases() {
    std::vector<std::pair<PatternPtr, ExprPtr>> cases;
    do {
      auto pattern = co_await consume_pattern();
      co_await consume(TokenType::TO_EXPR, "match expression");
      cases.emplace_back(std::move(pattern), co_await consume_expr());
    } while (co_await match(TokenType::PIPE));
    co_return cases;
  }

  subtask<Token, std::unique_ptr<FnExpr>> consume_fn_expr() {
    Token& first = co_await consume(TokenType::KW_FN, "fn expression");
    co_return std::make_unique<FnExpr>(first.location,
                                       co_await consume_cases());
  }

  subtask<Token, DeclPtr> consume_decl() {
    const Token* first = co_await peek();
    assert(first);
    switch (first->type) {
      case TokenType::KW_VAL:
        co_return co_await consume_val_decl();

      case TokenType::KW_DATATYPE:
        co_return co_await consume_dtype_decl();

      default:
        error(
            fmt::format("Expected decl but got token of type {}", first->type),
            *first);
    }
  }

  subtask<Token, DeclPtr> consume_val_decl() {
    const Location& location =
        (co_await consume(TokenType::KW_VAL, "val declaration")).get().location;
    auto explicit_type_vars = co_await consume_type_id_seq();
    std::sort(begin(explicit_type_vars), end(explicit_type_vars));
    std::vector<std::unique_ptr<ValBind>> bindings;
    bool is_recursive = false;
    do {
      bindings.push_back(co_await consume_val_bind(is_recursive));
      is_recursive = is_recursive || bindings.back()->rec;
    } while (co_await match(TokenType::KW_AND));
    co_return std::make_unique<ValDecl>(location, std::move(bindings),
                                        std::move(explicit_type_vars));
  }

  subtask<Token, std::vector<std::u8string>> consume_type_id_seq() {
    std::vector<std::u8string> types;
    if (co_await match(TokenType::ID_TYPE)) {
      types.push_back(move_string(tokens.back()));
    } else if (has_type(co_await peek(), TokenType::LPAREN) &&
               has_type(co_await peek(2), TokenType::ID_TYPE)) {
      std::set<std::u8string> types_deduped;
      co_await advance();
      do {
        auto s = move_string(
            (co_await consume(TokenType::ID_TYPE, "type id sequence")).get());
        types.push_back(s);
        if (!types_deduped.insert(s).second) {
          error("type id sequence contains duplicate type ids", tokens.back());
        }
      } while (co_await match(TokenType::COMMA));
      if (types.size() == 1) {
        error("Illegal type id sequence with single type id in parentheses",
              tokens.back());
      }
      co_await consume(TokenType::RPAREN, "type id sequence");
    }
    co_return types;
  }

  subtask<Token, std::unique_ptr<ValBind>> consume_val_bind(bool is_recursive) {
    const Location location = (co_await peek())->location;
    const bool rec = co_await match(TokenType::KW_REC);
    auto pattern = co_await consume_pattern();
    co_await consume(TokenType::EQUALS, "valbind declaration");
    ExprPtr expr = rec || is_recursive ? co_await consume_fn_expr()
                                       : co_await consume_expr();
    co_return std::make_unique<ValBind>(location, std::move(pattern),
                                        std::move(expr), rec);
  }

  subtask<Token, DeclPtr> consume_dtype_decl() {
    const Location& location =
        (co_await consume(TokenType::KW_DATATYPE, "datatype declaration"))
            .get()
            .location;
    std::vector<std::unique_ptr<DtypeBind>> bindings;
    do {
      bindings.push_back(co_await consume_dtype_bind());
    } while (co_await match(TokenType::KW_AND));
    check_no_doublebind(bindings);
    co_return std::make_unique<DtypeDecl>(location, std::move(bindings));
  }

  subtask<Token, std::unique_ptr<DtypeBind>> consume_dtype_bind() {
    const Location& location = (co_await peek())->location;
    auto types = co_await consume_type_id_seq();
    Token& id = co_await consume(TokenType::ID_WORD, "dtype-bind");
    co_await consume(TokenType::EQUALS, "dtype-bind");
    std::vector<std::unique_ptr<ConBind>> constructors;
    do {
      constructors.push_back(co_await consume_con_bind());
    } while (co_await match(TokenType::PIPE));
    check_type_vars(location, types, constructors);
    auto type_name = move_string(id);
    check_names(location, type_name, constructors);
    co_return std::make_unique<DtypeBind>(location, std::move(type_name),
                                          std::move(types),
                                          std::move(constructors));
  }

  subtask<Token, std::unique_ptr<ConBind>> consume_con_bind() {
    switch ((co_await peek())->type) {
      case TokenType::ID_WORD: {
        // This could be a type expression: foo list list list list list...
        std::size_t lookahead = 2;
        while (has_type(co_await peek(lookahead), TokenType::ID_WORD)) {
          ++lookahead;
        }
        if (has_type(co_await peek(lookahead), TokenType::ID_OP)) {
          co_return co_await consume_infix_con_bind();
        }
        Token& id = co_await advance();
        std::unique_ptr<TypeExpr> param;
        if (co_await match(TokenType::KW_OF)) {
          param = co_await consume_type();
        }
        co_return std::make_unique<ConBind>(id.location, move_string(id),
                                            std::move(param), false, false);
      }

      case TokenType::ID_OP: {
        Token& id = co_await advance();
        auto param = co_await consume_type();
        co_return std::make_unique<ConBind>(id.location, move_string(id),
                                            std::move(param), true, true);
      }

      case TokenType::LPAREN: {
        const Token* const first = co_await peek(2);
        if (first->type == TokenType::KW_PREFIX ||
            first->type == TokenType::ID_OP) {
          const Location& location = (co_await advance()).get().location;
          const bool prefix = co_await match(TokenType::KW_PREFIX);
          Token& id = co_await consume(TokenType::ID_OP, "con-bind paren op");
          co_await consume(TokenType::RPAREN, "con-bind paren op");
          TypeExprPtr param;
          if (co_await match(TokenType::KW_OF)) {
            param = co_await consume_type();
          }
          co_return std::make_unique<ConBind>(location, move_string(id),
                                              std::move(param), true, prefix);
        } else {
          co_return co_await consume_infix_con_bind();
        }
      }

      default:
        co_return co_await consume_infix_con_bind();
    }
  }

  subtask<Token, std::unique_ptr<ConBind>> consume_infix_con_bind() {
    std::vector<TypeExprPtr> types;
    types.push_back(co_await consume_type());
    Token& id = co_await consume(TokenType::ID_OP, "con-bind infix op");
    types.push_back(co_await consume_type());
    const Location& location = types.front()->location;
    co_return std::make_unique<ConBind>(
        location, move_string(id),
        std::make_unique<TupleTypeExpr>(location, std::move(types)), true,
        false);
  }

  subtask<Token, PatternPtr> consume_pattern() {
    const Token* const second = co_await peek(2);
    const Token* const first = co_await peek();
    if (has_type(first, TokenType::ID_WORD) &&
        (has_type(second, TokenType::COLON) ||
         has_type(second, TokenType::KW_AS))) {
      Token& id = co_await advance();
      TypeExprPtr type;
      if (co_await match(TokenType::COLON)) {
        type = co_await consume_type();
      }
      if (co_await match(TokenType::KW_AS)) {
        auto pattern = std::make_unique<LayeredPattern>(
            id.location, move_string(id), co_await consume_pattern());
        if (type) {
          co_return std::make_unique<TypedPattern>(
              id.location, std::move(pattern), std::move(type));
        }
        co_return pattern;
      }
      co_return std::make_unique<TypedPattern>(id.location, make_id_pattern(id),
                                               std::move(type));
    }
    auto pattern = co_await consume_left_pattern();
    // TODO: support infix precedence
    if (co_await match(TokenType::COLON)) {
      const Location& location = pattern->location;
      co_return std::make_unique<TypedPattern>(location, std::move(pattern),
                                               co_await consume_type());
    }
    co_return pattern;
  }

  subtask<Token, PatternPtr> consume_left_pattern() {
    const Token* const first = co_await peek();
    const Location location = first->location;
    auto maybe_id = co_await match_parenthesized_op_pattern(true);
    if (!maybe_id && (has_type(first, TokenType::QUAL_ID_WORD) ||
                      has_type(first, TokenType::ID_WORD))) {
      maybe_id = make_id_pattern(co_await advance());
    }
    if (maybe_id) {
      if (can_start_atomic_pattern(co_await peek())) {
        auto pattern = co_await consume_atomic_pattern();
        co_return std::make_unique<DatatypePattern>(
            location, std::move(maybe_id), std::move(pattern));
      } else if (maybe_id->qualifiers.empty() || !maybe_id->is_op) {
        co_return maybe_id;
      } else {
        error("Qualified operator not permitted as atomic pattern", location);
      }
    }
    co_return co_await consume_atomic_pattern();
  }

  subtask<Token, std::unique_ptr<IdentifierPattern>>
  match_parenthesized_op_pattern(bool allow_qualified) {
    const Token* const first = co_await peek();
    assert(first);

    if (first->type != TokenType::LPAREN) co_return nullptr;

    const Token* const second = co_await peek(2);

    if (has_type(second, TokenType::KW_PREFIX)) {
      co_await advance();
      co_await advance();
      Token& id = allow_qualified
                      ? co_await consume({QUAL_OP_TYPES}, "prefix op")
                      : co_await consume({NON_QUAL_OP_TYPES}, "prefix op");
      co_await consume(TokenType::RPAREN, "prefix op");
      co_return make_id_pattern(id, true);
    }

    if (is_op(second, allow_qualified) &&
        has_type(co_await peek(3), TokenType::RPAREN)) {
      co_await advance();
      Token& id = co_await advance();
      co_await advance();
      co_return make_id_pattern(id, false);
    }

    co_return nullptr;
  }

  subtask<Token, PatternPtr> consume_atomic_pattern() {
    auto maybe_op = co_await match_parenthesized_op_pattern(false);
    if (maybe_op) co_return maybe_op;

    const Token* const first = co_await peek();
    assert(first);

    switch (first->type) {
      case TokenType::KW_UNDERSCORE:
        co_return std::make_unique<WildcardPattern>(
            (co_await advance()).get().location);

      case TokenType::ILITERAL:
      case TokenType::STRING: {
        auto expr = co_await consume_atomic_expr();
        const Location& location = expr->location;
        co_return std::make_unique<LiteralPattern>(location, std::move(expr));
      }

      case TokenType::ID_WORD:
      case TokenType::QUAL_ID_WORD:
        co_return make_id_pattern(co_await advance(), false);

      case TokenType::LBRACE:
        co_return co_await consume_record_pattern();

      case TokenType::LBRACKET:
        co_return co_await consume_list_pattern();

      case TokenType::LPAREN:
        co_return co_await consume_paren_pattern();

      default:
        error("Unexpected token when parsing atomic pattern",
              co_await advance());
    }
  }

  subtask<Token, PatternPtr> consume_record_pattern() {
    std::vector<std::unique_ptr<RecRowPattern>> rows;
    std::set<std::u8string> labels;
    bool has_wildcard = false;
    const Location& location =
        (co_await consume(TokenType::LBRACE, "record pattern")).get().location;
    if (!co_await match(TokenType::RBRACE)) {
      do {
        if (co_await match(TokenType::ELLIPSIS)) {
          if (has_wildcard) {
            error("'...' may not appear twice in a single pattern.",
                  tokens.back());
          } else {
            has_wildcard = true;
          }
        } else {
          Token& label =
              co_await consume(TokenType::ID_WORD, "record row pattern");
          std::u8string label_name = get<std::u8string>(label.aux);
          PatternPtr pattern;
          if (co_await match(TokenType::EQUALS)) {
            pattern = co_await consume_pattern();
          } else {
            TypeExprPtr type;
            if (co_await match(TokenType::COLON)) {
              type = co_await consume_type();
            }
            if (co_await match(TokenType::KW_AS)) {
              pattern = std::make_unique<LayeredPattern>(
                  label.location, label_name, co_await consume_pattern());
            } else {
              pattern =
                  make_id_pattern(label.location, {}, label_name, false, false);
            }
            if (type) {
              pattern = std::make_unique<TypedPattern>(
                  label.location, std::move(pattern), std::move(type));
            }
          }
          auto insres = labels.insert(label_name);
          if (!insres.second) {
            error(fmt::format("Label '{}' was specified twice in pattern",
                              to_std_string(label_name)),
                  label);
          }
          rows.push_back(std::make_unique<RecRowPattern>(
              label.location, move_string(label), std::move(pattern)));
        }
      } while (co_await match(TokenType::COMMA));
      co_await consume(TokenType::RBRACE, "record pattern");
    }
    co_return std::make_unique<RecordPattern>(location, std::move(rows),
                                              has_wildcard);
  }

  subtask<Token, PatternPtr> consume_list_pattern() {
    const Location& location =
        (co_await consume(TokenType::LBRACKET, "list pattern")).get().location;
    std::vector<PatternPtr> patterns;
    if (!co_await match(TokenType::RBRACKET)) {
      do {
        patterns.push_back(co_await consume_pattern());
      } while (co_await match(TokenType::COMMA));
      co_await consume(TokenType::RBRACKET, "list pattern");
    }
    co_return std::make_unique<ListPattern>(location, std::move(patterns));
  }

  subtask<Token, PatternPtr> consume_paren_pattern() {
    const Location& location =
        (co_await consume(TokenType::LPAREN, "parenthesized pattern"))
            .get()
            .location;
    if (co_await match(TokenType::RPAREN)) {
      co_return std::make_unique<TuplePattern>(location,
                                               std::vector<PatternPtr>{});
    }
    if (co_await match(TokenType::KW_PREFIX)) {
      Token& id = co_await consume({NON_QUAL_OP_TYPES}, "prefix op pattern");
      co_await consume(TokenType::RPAREN, "prefix op pattern");
      co_return make_id_pattern(id, true);
    }
    if (is_op(co_await peek(), false) &&
        has_type(co_await peek(2), TokenType::RPAREN)) {
      Token& id = co_await advance();
      co_await advance();
      co_return make_id_pattern(id, false);
    }

    std::vector<PatternPtr> patterns;
    do {
      patterns.push_back(co_await consume_pattern());
    } while (co_await match(TokenType::COMMA));
    co_await consume(TokenType::RPAREN, "parenthesized pattern");
    if (patterns.size() == 1) {
      co_return std::move(patterns.front());
    }
    co_return std::make_unique<TuplePattern>(location, std::move(patterns));
  }

  subtask<Token, TypeExprPtr> consume_type() {
    auto t = co_await consume_tuple_type();
    const Location location = t->location;
    if (co_await match(TokenType::TO_TYPE)) {
      auto ret = co_await consume_type();

      co_return std::make_unique<FuncTypeExpr>(location, std::move(t),
                                               std::move(ret));
    }
    co_return t;
  }

  subtask<Token, TypeExprPtr> consume_tuple_type() {
    std::vector<TypeExprPtr> types;
    do {
      types.push_back(co_await consume_atomic_type());
    } while (co_await match(TokenType::ASTERISK));
    if (types.size() == 1) {
      co_return std::move(types.front());
    }
    const Location& location = types.front()->location;
    co_return std::make_unique<TupleTypeExpr>(location, std::move(types));
  }

  subtask<Token, TypeExprPtr> consume_atomic_type() {
    const Token* const first = co_await peek();
    assert(first);
    TypeExprPtr type;
    switch (first->type) {
      case TokenType::ID_TYPE: {
        Token& t = co_await advance();
        type = std::make_unique<VarTypeExpr>(t.location, move_string(t));
        break;
      }

      case TokenType::LBRACE:
        type = co_await consume_record_type();
        break;

      case TokenType::LPAREN:
        type = co_await consume_paren_type();
        break;

      case TokenType::QUAL_ID_WORD:
      case TokenType::ID_WORD: {
        Token& t = co_await advance();
        type = make_tycon_type(t.location, t);
        break;
      }

      default:
        error("Unexpected token in type expression", co_await advance());
    }
    const Location& location = type->location;
    while (co_await match({TokenType::QUAL_ID_WORD, TokenType::ID_WORD})) {
      type = make_tycon_type(location, tokens.back(), std::move(type));
    }
    co_return type;
  }

  subtask<Token, TypeExprPtr> consume_record_type() {
    std::vector<std::pair<std::u8string, TypeExprPtr>> rows;
    std::set<std::u8string> labels;
    const Location& location =
        (co_await consume(TokenType::LBRACE, "record type expresion"))
            .get()
            .location;
    if (!co_await match(TokenType::RBRACE)) {
      do {
        Token& id =
            co_await consume(TokenType::ID_WORD, "record row type expression");
        co_await consume(TokenType::COLON, "record row type expression");
        rows.emplace_back(move_string(id), co_await consume_type());
        auto insres = labels.insert(rows.back().first);
        if (!insres.second) {
          error(fmt::format("Label '{}' bound twice in record type expression",
                            to_std_string(rows.back().first)),
                id);
        }
      } while (co_await match(TokenType::COMMA));
      co_await consume(TokenType::RBRACE, "record type expression");
    }
    co_return std::make_unique<RecordTypeExpr>(location, std::move(rows));
  }

  subtask<Token, TypeExprPtr> consume_paren_type() {
    const Location& location =
        (co_await consume(TokenType::LPAREN, "parenthesized type expresion"))
            .get()
            .location;
    std::vector<TypeExprPtr> types;
    do {
      types.push_back(co_await consume_type());
    } while (co_await match(TokenType::COMMA));
    co_await consume(TokenType::RPAREN, types.size() == 1
                                            ? "parenthesized type expresion"
                                            : "type sequence");
    if (types.size() == 1) {
      co_return std::move(types.front());
    }
    co_return make_tycon_type(
        location,
        co_await consume({TokenType::ID_WORD, TokenType::QUAL_ID_WORD},
                         "type constructor expression"),
        std::move(types));
  }
};

parser::~parser() = default;

bool parser::requires_more_input() const {
  return next_token_ && !next_token_->tokens.empty();
}

processor::processor<Token, Expected<TopDeclPtr>> parser::parse() {
  while (true) {
    Expected<TopDeclPtr> result;
    next_token n;
    next_token_ = &n;
    try {
      result = co_await n();
    } catch (ParsingError& e) {
      result = std::make_exception_ptr(e);
    } catch (eof) {
      co_return;
    } catch (reset) {
      continue;
    }
    next_token_ = nullptr;
    co_yield std::move(result);
  }
}

processor::processor<Token, Expected<TopDeclPtr>> parse() {
  parser p;
  auto s = p.parse().as_subprocess();
  while (!co_await s.done()) {
    co_yield co_await s;
  }
}

}  // namespace emil
