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

#include <cassert>
#include <cstddef>
#include <iterator>
#include <numeric>
#include <optional>
#include <ranges>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "emil/ast.h"
#include "emil/bigint.h"
#include "emil/collections.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/typed_ast.h"
#include "emil/types.h"

namespace emil {

ElaborationError::ElaborationError(std::string msg, const Location &location)
    : msg(std::move(msg)),
      location(location),
      full_msg(fmt::format("{}:{}: error: {}", this->location.filename,
                           this->location.line, this->msg)) {}

Typer::Typer()
    : stamp_generator_(),
      builtins_(typing::BuiltinTypes::create(stamp_generator_)) {}

namespace {

collections::ConsPtr<ManagedString> consify(
    const std::vector<std::u8string> &names) {
  collections::ConsPtr<ManagedString> l = nullptr;
  for (const auto &n : std::ranges::reverse_view(names)) {
    l = cons(make_string(n), l);
  }
  return l;
}

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

void TopDeclElaborator::visitDeclTopDecl(const DeclTopDecl &node) {
  auto r = typer_.elaborate(B->as_context(), *node.decl);
  B = B + r.env;
  typed = std::make_unique<TDeclTopDecl>(node.location, std::move(r.decl));
}

}  // namespace

Typer::elaborate_topdecl_t Typer::elaborate(managed_ptr<typing::Basis> B,
                                            const TopDecl &topdec) {
  TopDeclElaborator v(*this, std::move(B));
  topdec.accept(v);
  return {std::move(v.B), std::move(v.typed)};
}

namespace {

class ExprElaborator : public Expr::Visitor {
 public:
  const managed_ptr<typing::Context> C;
  std::unique_ptr<TExpr> typed;
  typing::Substitutions new_substitutions =
      collections::managed_map<typing::Stamp, typing::Type>({});

  ExprElaborator(Typer &typer, managed_ptr<typing::Context> C,
                 typing::Substitutions &substitutions,
                 std::uint64_t maximum_type_name_id)
      : C(std::move(C)),
        typer_(typer),
        substitutions_(substitutions),
        maximum_type_name_id_(maximum_type_name_id) {}

  DECLARE_EXPR_V_FUNCS;

 private:
  Typer &typer_;
  typing::Substitutions &substitutions_;
  std::uint64_t maximum_type_name_id_;

  struct elaborate_rec_row_t {
    std::unique_ptr<TRecRowExpr> elaborated_row;
    typing::Substitutions new_substitutions;
  };

  elaborate_rec_row_t elaborate_rec_row(const RecRowExpr &node) const;

  struct elaborate_match_t {
    std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
        cases;
    managed_ptr<typing::FunctionType> unified_type;
  };

  elaborate_match_t elaborate_match(
      const std::vector<
          std::pair<std::unique_ptr<Pattern>, std::unique_ptr<Expr>>> &) {
    throw std::logic_error("Not implemented!");
  }
};

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
  std::vector<std::unique_ptr<TExpr>> str_substitutions;
  str_substitutions.reserve(node.substitutions.size());
  for (const auto &ns : node.substitutions) {
    auto e = typer_.elaborate(C, *ns, substitutions_, maximum_type_name_id_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &ss : str_substitutions) {
        ss = ss->apply_substitutions(e.new_substitutions);
      }
    }
    str_substitutions.push_back(std::move(e.expr));
  }
  // TODO: Unify subexpression type with printable
  typed = std::make_unique<TFstringLiteralExpr>(
      node.location, typer_.builtins().string_type(), std::move(segments),
      std::move(str_substitutions));
}

std::string id_to_string(const std::vector<std::u8string> &qualifiers,
                         std::u8string id) {
  if (qualifiers.empty()) return to_std_string(id);
  std::string out;
  const auto size = std::accumulate(
      cbegin(qualifiers), cend(qualifiers), id.size() + qualifiers.size(),
      [](auto acc, const auto &q) { return acc + q.size(); });
  out.reserve(size);
  for (const auto &q : qualifiers) {
    out += to_std_string(q);
    out += '.';
  }
  out += to_std_string(id);
  return out;
}

void ExprElaborator::visitIdentifierExpr(const IdentifierExpr &node) {
  const auto id = typing::canonicalize_val_id(node.identifier, node.is_op,
                                              node.is_prefix_op);
  const auto val = C->env()->lookup_val(node.qualifiers, id);
  if (!val)
    throw ElaborationError(
        fmt::format("{} is not defined", id_to_string(node.qualifiers, id)),
        node.location);
  typed = std::make_unique<TIdentifierExpr>(
      node.location, (*val)->scheme()->instantiate(typer_.stamper()),
      (*val)->status(), consify(node.qualifiers), make_string(id));
}

void ExprElaborator::visitRecRowExpr(const RecRowExpr &) {
  throw std::logic_error("Unreachable.");
}

ExprElaborator::elaborate_rec_row_t ExprElaborator::elaborate_rec_row(
    const RecRowExpr &node) const {
  auto e =
      typer_.elaborate(C, *node.val, substitutions_, maximum_type_name_id_);
  auto t = e.expr->type;
  return {.elaborated_row = std::make_unique<TRecRowExpr>(
              node.location, std::move(t), make_string(node.label),
              std::move(e.expr)),
          .new_substitutions = e.new_substitutions};
}

void ExprElaborator::visitRecordExpr(const RecordExpr &node) {
  std::vector<std::unique_ptr<TRecRowExpr>> exprs;
  exprs.reserve(node.rows.size());
  for (const auto &r : node.rows) {
    auto e = elaborate_rec_row(*r);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions_as_rec_row(e.new_substitutions);
      }
    }
    exprs.push_back(std::move(e.elaborated_row));
  }
  typing::StringMap<typing::Type> rows =
      collections::managed_map<ManagedString, typing::Type>({});
  for (const auto &expr : exprs) {
    rows = rows->insert(expr->label, expr->type).first;
  }
  typed = std::make_unique<TRecordExpr>(
      node.location, typer_.builtins().record_type(rows), std::move(exprs));
}

void ExprElaborator::visitUnitExpr(const UnitExpr &node) {
  typed = std::make_unique<TTupleExpr>(
      node.location,
      typer_.builtins().tuple_type(collections::make_array<typing::Type>({})),
      std::vector<std::unique_ptr<TExpr>>{});
}

void ExprElaborator::visitTupleExpr(const TupleExpr &node) {
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate(C, *ne, substitutions_, maximum_type_name_id_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions);
      }
    }
    exprs.push_back(std::move(e.expr));
  }
  auto types = make_managed<collections::ManagedArray<typing::Type>>(
      exprs.size(), [&](std::size_t i) { return exprs[i]->type; });
  typed = std::make_unique<TTupleExpr>(
      node.location, typer_.builtins().tuple_type(types), std::move(exprs));
}

void ExprElaborator::visitSequencedExpr(const SequencedExpr &node) {
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate(C, *ne, substitutions_,
                              typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions);
      }
    }
    exprs.push_back(std::move(e.expr));
  }
  auto type = exprs.back()->type;
  if (type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in sequenced expression (type escape).",
        node.location);
  }
  typed =
      std::make_unique<TSequencedExpr>(node.location, type, std::move(exprs));
}

void ExprElaborator::visitListExpr(const ListExpr &node) {
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  typing::TypePtr type =
      make_managed<typing::UndeterminedType>(typer_.new_stamp());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate(C, *ne, substitutions_, maximum_type_name_id_);
    auto u = typing::unify(type, e.expr->type, substitutions_,
                           maximum_type_name_id_, maximum_type_name_id_);
    if (!u.new_substitutions->empty()) {
      e.expr = e.expr->apply_substitutions(u.new_substitutions);
    }
    if (!u.new_substitutions->empty() || !e.new_substitutions->empty()) {
      auto new_subs = e.new_substitutions | u.new_substitutions;
      new_substitutions = new_substitutions | new_subs;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(new_subs);
      }
    }
    exprs.push_back(std::move(e.expr));
  }
  typed = std::make_unique<TListExpr>(node.location, type, std::move(exprs));
}

void ExprElaborator::visitLetExpr(const LetExpr &node) {
  std::vector<std::unique_ptr<TDecl>> decls;
  decls.reserve(node.decls.size());
  managed_ptr<typing::Context> Cprime = C;
  for (const auto &nd : node.decls) {
    auto e = typer_.elaborate(Cprime, *nd, substitutions_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &decl : decls) {
        decl = decl->apply_substitutions(e.new_substitutions);
      }
    }
    Cprime = Cprime + e.env;
    decls.push_back(std::move(e.decl));
  }

  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate(Cprime, *ne, substitutions_,
                              typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &decl : decls) {
        decl = decl->apply_substitutions(e.new_substitutions);
      }
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions);
      }
    }
    exprs.push_back(std::move(e.expr));
  }

  auto type = exprs.back()->type;
  if (type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in let expression (type escape).", node.location);
  }

  typed = std::make_unique<TLetExpr>(node.location, type, std::move(decls),
                                     std::move(exprs));
}

class GetFunctionVisitor : public typing::TypeVisitor {
 public:
  const typing::FunctionType *fn = nullptr;
  typing::Substitutions new_substitutions =
      collections::managed_map<typing::Stamp, typing::Type>({});

  explicit GetFunctionVisitor(Typer &typer) : typer_(typer) {}

  void visit(const typing::TypeWithAgeRestriction &t) override {
    t.type()->accept(*this);
  }

  void visit(const typing::UndeterminedType &t) override {
    auto p = make_managed<typing::UndeterminedType>(typer_.new_stamp());
    auto r = make_managed<typing::UndeterminedType>(typer_.new_stamp());
    auto fnptr = make_managed<typing::FunctionType>(p, r);
    new_substitutions =
        new_substitutions
            ->insert(t.stamp(), make_managed<typing::TypeWithAgeRestriction>(
                                    fnptr, t.stamp()->id()))
            .first;
    fn = &*fnptr;
  }

  void visit(const typing::FunctionType &t) override { fn = &t; }

  void visit(const typing::TypeVar &) override {}
  void visit(const typing::TupleType &) override {}
  void visit(const typing::RecordType &) override {}
  void visit(const typing::ConstructedType &) override {}

 private:
  Typer &typer_;
};

struct get_function_t {
  const typing::FunctionType *fn;
  typing::Substitutions new_substitutions;
};

/**
 * Gets a pointer to a function type from t.
 *
 * If t is an undetermined type, introduces a substitution. If t
 * cannot be unified with a function type, the result's fn field will
 * be null.
 */
get_function_t get_function(typing::TypePtr t, Typer &typer) {
  GetFunctionVisitor v{typer};
  t->accept(v);
  return {v.fn, v.new_substitutions};
}

class GetIdentifierVisitor : public TExpr::Visitor {
 public:
  const TIdentifierExpr *id;

  void visit(const TBigintLiteralExpr &) override { id = nullptr; }
  void visit(const TIntLiteralExpr &) override { id = nullptr; }
  void visit(const TFpLiteralExpr &) override { id = nullptr; }
  void visit(const TStringLiteralExpr &) override { id = nullptr; }
  void visit(const TCharLiteralExpr &) override { id = nullptr; }
  void visit(const TFstringLiteralExpr &) override { id = nullptr; }
  void visit(const TIdentifierExpr &v) override { id = &v; }
  void visit(const TRecRowExpr &) override { id = nullptr; }
  void visit(const TRecordExpr &) override { id = nullptr; }
  void visit(const TTupleExpr &) override { id = nullptr; }
  void visit(const TSequencedExpr &) override { id = nullptr; }
  void visit(const TListExpr &) override { id = nullptr; }
  void visit(const TLetExpr &) override { id = nullptr; }
  void visit(const TApplicationExpr &) override { id = nullptr; }
  void visit(const TCaseExpr &) override { id = nullptr; }
  void visit(const TFnExpr &) override { id = nullptr; }
};

/** Returns null if expr is not an identifier. */
const TIdentifierExpr *get_identifier(const TExpr &expr) {
  GetIdentifierVisitor v;
  expr.accept(v);
  return v.id;
}

class GetTypenameVisitor : public typing::TypeVisitor {
 public:
  managed_ptr<typing::TypeName> name = nullptr;

  void visit(const typing::TypeWithAgeRestriction &t) override {
    t.type()->accept(*this);
  }

  void visit(const typing::ConstructedType &t) override { name = t.name(); }

  void visit(const typing::UndeterminedType &) override {}
  void visit(const typing::FunctionType &) override {}
  void visit(const typing::TypeVar &) override {}
  void visit(const typing::TupleType &) override {}
  void visit(const typing::RecordType &) override {}
};

managed_ptr<typing::TypeName> get_type_name(typing::TypePtr type) {
  GetTypenameVisitor v;
  type->accept(v);
  assert(v.name);
  return v.name;
}

bool is_nonexpansive_application(
    const std::vector<std::unique_ptr<TExpr>> &exprs, Typer &typer) {
  if (exprs.size() != 2) return false;
  if (!exprs.back()->is_nonexpansive) return false;
  const auto *id = get_identifier(*exprs.front());
  if (!id) return false;
  switch (id->status) {
    case typing::IdStatus::Variable:
      return false;

    case typing::IdStatus::Exception:
      return true;

    case typing::IdStatus::Constructor: {
      auto gf = get_function(id->type, typer);
      assert(gf.new_substitutions->empty());
      return get_type_name(gf.fn->result())->stamp() !=
             typer.builtins().ref_name()->stamp();
    }
  }
}

void ExprElaborator::visitApplicationExpr(const ApplicationExpr &node) {
  assert(node.exprs.size() >= 2);
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate(C, *ne, substitutions_,
                              typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
    auto new_subs = e.new_substitutions;
    if (!exprs.empty()) {
      auto gf = get_function(exprs.back()->type, typer_);
      if (!gf.fn) {
        throw ElaborationError(
            fmt::format("Expression must be a function but instead is {}.",
                        to_std_string(typing::print_type(exprs.back()->type))),
            exprs.back()->location);
      }
      substitutions_ = substitutions_ | gf.new_substitutions;
      if (!gf.new_substitutions->empty()) {
        e.expr = e.expr->apply_substitutions(gf.new_substitutions);
        new_subs = new_subs | gf.new_substitutions;
      }
      auto u = typing::unify(gf.fn->result(), e.expr->type, substitutions_,
                             typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                             typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
      if (!u.new_substitutions->empty()) {
        e.expr = e.expr->apply_substitutions(u.new_substitutions);
        new_subs = new_subs | u.new_substitutions;
      }
    }
    if (!new_subs->empty()) {
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(new_subs);
      }
      new_substitutions = new_substitutions | new_subs;
    }
    exprs.push_back(std::move(e.expr));
  }

  auto type = exprs.back()->type;
  if (type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in function application expression (type "
        "escape).",
        node.location);
  }

  const bool is_nonexpansive = is_nonexpansive_application(exprs, typer_);
  typed = std::make_unique<TApplicationExpr>(node.location, type,
                                             is_nonexpansive, std::move(exprs));
}

void ExprElaborator::visitCaseExpr(const CaseExpr &node) {
  auto m = elaborate_match(node.cases);
  auto e = typer_.elaborate(C, *node.expr, substitutions_,
                            typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
  auto u = typing::unify(m.unified_type->param(), e.expr->type, substitutions_,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION);
  if (!u.new_substitutions->empty()) {
    e.expr = e.expr->apply_substitutions(u.new_substitutions);
  }
  auto new_subs = e.new_substitutions | u.new_substitutions;
  auto type = m.unified_type->result();
  if (!new_subs->empty()) {
    for (auto &c : m.cases) {
      c.first = c.first->apply_substitutions(new_subs);
      c.second = c.second->apply_substitutions(new_subs);
    }
    type = typing::apply_substitutions(type, new_subs);
    new_substitutions = new_substitutions | new_subs;
  }
  if (type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in case expression (type escape).",
        node.location);
  }
  typed = std::make_unique<TCaseExpr>(node.location, type, std::move(e.expr),
                                      std::move(m.cases));
}

void ExprElaborator::visitFnExpr(const FnExpr &node) {
  auto m = elaborate_match(node.cases);
  if (m.unified_type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in fn expression (type escape).", node.location);
  }
  typed = std::make_unique<TFnExpr>(node.location, m.unified_type,
                                    std::move(m.cases));
}

void ExprElaborator::visitTypedExpr(const TypedExpr &node) {
  auto t = typer_.elaborate_type_expr(C, *node.type);
  auto e =
      typer_.elaborate(C, *node.expr, substitutions_, maximum_type_name_id_);
  new_substitutions = new_substitutions | e.new_substitutions;
  auto u = typing::unify(t, e.expr->type, substitutions_, maximum_type_name_id_,
                         maximum_type_name_id_);
  if (!u.new_substitutions->empty()) {
    e.expr = e.expr->apply_substitutions(u.new_substitutions);
    new_substitutions = new_substitutions | u.new_substitutions;
  }
  typed = std::move(e.expr);
}

}  // namespace

managed_ptr<typing::Stamp> Typer::new_stamp() { return stamp_generator_(); }

const typing::BuiltinTypes &Typer::builtins() const { return builtins_; }

}  // namespace emil
