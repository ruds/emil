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

#include "emil/typer.h"

#include <fmt/core.h>

#include <algorithm>
#include <iterator>
#include <stdexcept>
#include <string>
#include <vector>

#include "emil/ast.h"
#include "emil/bigint.h"
#include "emil/cons.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/typed_ast.h"
#include "emil/types.h"

namespace emil {

namespace {

class TopDeclElaborator : public TopDecl::Visitor {
 public:
  managed_ptr<typing::Basis> B;
  std::unique_ptr<TTopDecl> typed;

  TopDeclElaborator(Typer &typer, managed_ptr<typing::Basis> B)
      : B(std::move(B)), typer_(typer) {}

  DECLARE_TOPDECL_V_FUNCS;

 private:
  Typer &typer_;
};

class DeclElaborator : public Decl::Visitor {
 public:
  const managed_ptr<typing::Context> C;
  managed_ptr<typing::Env> E;
  std::unique_ptr<TDecl> typed;

  DeclElaborator(Typer &typer, managed_ptr<typing::Context> C)
      : C(std::move(C)), typer_(typer) {}

  DECLARE_DECL_V_FUNCS;

 private:
  Typer &typer_;
};

class ExprElaborator : public Expr::Visitor {
 public:
  const managed_ptr<typing::Context> C;
  std::unique_ptr<TExpr> typed;

  ExprElaborator(Typer &typer, managed_ptr<typing::Context> C)
      : C(std::move(C)), typer_(typer) {}

  DECLARE_EXPR_V_FUNCS;

 private:
  Typer &typer_;
};

void TopDeclElaborator::visitEmptyTopDecl(const EmptyTopDecl &node) {
  typed = std::make_unique<TEmptyTopDecl>(node.location);
}

void TopDeclElaborator::visitEndOfFileTopDecl(const EndOfFileTopDecl &node) {
  typed = std::make_unique<TEndOfFileTopDecl>(node.location);
}

void TopDeclElaborator::visitExprTopDecl(const ExprTopDecl &node) {
  typed = std::make_unique<TExprTopDecl>(
      node.location, typer_.elaborate(B->as_context(), *node.expr));
}

void TopDeclElaborator::visitDeclTopDecl(const DeclTopDecl & /*node*/) {
  throw std::runtime_error("visitDeclTopDecl is not implemented.");
  /*
  auto r = typer_.elaborate(B->as_context(), *node.decl);
  B = B + r.first;
  typed = std::make_unique<TDeclTopDecl>(node.location, std::move(r.second));
   */
}

void ExprElaborator::visitBigintLiteralExpr(const BigintLiteralExpr &node) {
  managed_ptr<bigint> val;
  switch (node.val.base) {
    case 2:
      val = parse_bigint_binary(node.val.number);
      break;
    case 8:
      val = parse_bigint_octal(node.val.number);
      break;
    case 10:
      val = parse_bigint_decimal(node.val.number);
      break;
    case 16:
      val = parse_bigint_hex(node.val.number);
      break;
    default:
      throw std::logic_error(fmt::format("Bad bigint base: {}", node.val.base));
  }
  typed = std::make_unique<TBigintLiteralExpr>(
      node.location, typer_.builtins().bigint_type(), std::move(val));
}

void ExprElaborator::visitIntLiteralExpr(const IntLiteralExpr &node) {
  typed = std::make_unique<TIntLiteralExpr>(
      node.location, typer_.builtins().int_type(), node.val);
}

void ExprElaborator::visitFpLiteralExpr(const FpLiteralExpr &node) {
  typed = std::make_unique<TFpLiteralExpr>(
      node.location, typer_.builtins().float_type(), node.val);
}

void ExprElaborator::visitStringLiteralExpr(const StringLiteralExpr &node) {
  typed = std::make_unique<TStringLiteralExpr>(
      node.location, typer_.builtins().string_type(), make_string(node.val));
}

void ExprElaborator::visitCharLiteralExpr(const CharLiteralExpr &node) {
  typed = std::make_unique<TCharLiteralExpr>(
      node.location, typer_.builtins().char_type(), node.val);
}

void ExprElaborator::visitFstringLiteralExpr(const FstringLiteralExpr &node) {
  collections::ConsPtr<ManagedString> segments = nullptr;
  for (auto it = node.segments.rbegin(); it != node.segments.rend(); ++it) {
    cons(make_string(*it), segments);
  }
  std::vector<std::unique_ptr<TExpr>> substitutions;
  substitutions.reserve(node.substitutions.size());
  std::transform(node.substitutions.begin(), node.substitutions.end(),
                 std::back_inserter(substitutions),
                 [&](const auto &e) { return typer_.elaborate(C, *e); });
  // TODO: Unify subexpression type with printable
  typed = std::make_unique<TFstringLiteralExpr>(
      node.location, typer_.builtins().string_type(), std::move(segments),
      std::move(substitutions));
}

}  // namespace

Typer::Typer()
    : stamp_generator_(),
      builtins_(typing::BuiltinTypes::create(stamp_generator_)) {}

std::pair<managed_ptr<typing::Basis>, std::unique_ptr<TTopDecl>>
Typer::elaborate(managed_ptr<typing::Basis> B, const TopDecl &topdec) {
  TopDeclElaborator v(*this, std::move(B));
  topdec.accept(v);
  return std::make_pair(std::move(v.B), std::move(v.typed));
}

managed_ptr<typing::Stamp> Typer::new_stamp() { return stamp_generator_(); }

const typing::BuiltinTypes &Typer::builtins() const { return builtins_; }

}  // namespace emil
