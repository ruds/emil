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
#include <fmt/format.h>

#include <algorithm>
#include <cassert>
#include <compare>
#include <cstddef>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <ranges>
#include <set>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "emil/ast.h"
#include "emil/bigint.h"
#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/reporter.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/tree.h"
#include "emil/typed_ast.h"
#include "emil/types.h"

// IWYU pragma: no_include <__tree>

namespace emil {

ElaborationError::ElaborationError(std::string msg, const Location &location)
    : msg(std::move(msg)),
      location(location),
      full_msg(fmt::format("{}:{}: error: {}", this->location.filename,
                           this->location.line, this->msg)) {}

ElaborationError::ElaborationError(const typing::UnificationError &e,
                                   const Location &location)
    : msg(fmt::format("Unification error: {}", e.what())),
      location(location),
      full_msg(fmt::format("{}:{}: error: {}", this->location.filename,
                           this->location.line, e.what())) {}

Typer::Typer(Reporter &reporter)
    : stamp_generator_(),
      builtins_(typing::BuiltinTypes::create(stamp_generator_)),
      reporter_(reporter) {}

namespace {

template <typename StringRange>
typing::StringSet to_set(const StringRange &v) {
  auto ss = collections::managed_set<ManagedString>({});
  for (const auto &s : v) {
    ss = ss->insert(make_string(s)).first;
  }
  return ss;
}

using ImplicitlyScopedVars = Typer::ImplicitlyScopedVars;

ImplicitlyScopedVars scope_explicit_type_variables(const Decl &dec);
ImplicitlyScopedVars scope_explicit_type_variables(const Expr &exp);
ImplicitlyScopedVars scope_explicit_type_variables(const Pattern &pat);
ImplicitlyScopedVars scope_explicit_type_variables(const TypeExpr &ty);

template <typename C>
void merge_into(std::set<std::u8string> &l, const C &r) {
  auto lb = l.begin(), le = l.end();
  auto rb = r.begin(), re = r.end();
  while (lb != le && rb != re) {
    const auto c = *lb <=> *rb;
    if (c < 0) {
      ++lb;
    } else if (c > 0) {
      l.insert(lb, *rb++);
    } else {
      ++lb;
      ++rb;
    }
  }
  while (rb != re) {
    l.insert(lb, *rb++);
  }
}

void merge(ImplicitlyScopedVars &vars, ImplicitlyScopedVars &&new_vars) {
  auto lb = vars.begin(), le = vars.end();
  auto rb = new_vars.begin(), re = new_vars.end();
  auto cmp = std::compare_three_way();
  while (lb != le && rb != re) {
    const auto c = cmp(lb->first, rb->first);
    if (c < 0) {
      ++lb;
    } else if (c > 0) {
      vars.insert(lb, *rb++);
    } else {
      merge_into(lb++->second, std::move(rb++->second));
    }
  }
  while (rb != re) {
    vars.insert(lb, *rb++);
  }
}

template <typename C>
void remove_all(std::set<std::u8string> &l, const C &r) {
  auto lb = l.begin(), le = l.end();
  auto rb = r.begin(), re = r.end();
  while (lb != le && rb != re) {
    auto c = *lb <=> *rb;
    if (c < 0) {
      ++lb;
    } else if (c > 0) {
      ++rb;
    } else {
      lb = l.erase(lb);
      ++rb;
    }
  }
}

void remove_from_children(ImplicitlyScopedVars &vars,
                          const std::set<std::u8string> to_remove) {
  for (auto &entry : vars) {
    if (!entry.first) continue;
    remove_all(entry.second, to_remove);
  }
}

class DeclVarScoper : public Decl::Visitor {
 public:
  ImplicitlyScopedVars vars;

  void visitValDecl(const ValDecl &d) override {
    for (const auto &b : d.bindings) {
      merge(vars, scope_explicit_type_variables(*b->pat));
      merge(vars, scope_explicit_type_variables(*b->expr));
    }
    assert(std::ranges::is_sorted(d.explicit_type_vars));
    auto &scoped_vars = vars[nullptr];
    merge_into(scoped_vars, d.explicit_type_vars);
    remove_from_children(vars, scoped_vars);
    remove_all(scoped_vars, d.explicit_type_vars);
    vars[&d] = std::move(scoped_vars);
    vars.erase(nullptr);
  }
};

ImplicitlyScopedVars scope_explicit_type_variables(const Decl &dec) {
  DeclVarScoper v;
  dec.accept(v);
  return std::move(v.vars);
}

class ExprVarScoper : public Expr::Visitor {
 public:
  ImplicitlyScopedVars vars;

  void visitBigintLiteralExpr(const BigintLiteralExpr &) override {}
  void visitIntLiteralExpr(const IntLiteralExpr &) override {}
  void visitFpLiteralExpr(const FpLiteralExpr &) override {}
  void visitStringLiteralExpr(const StringLiteralExpr &) override {}
  void visitCharLiteralExpr(const CharLiteralExpr &) override {}
  void visitIdentifierExpr(const IdentifierExpr &) override {}
  void visitRecRowExpr(const RecRowExpr &) override {}
  void visitUnitExpr(const UnitExpr &) override {}

  void visitFstringLiteralExpr(const FstringLiteralExpr &e) override {
    for (const auto &s : e.substitutions) {
      s->accept(*this);
    }
  }

  void visitRecordExpr(const RecordExpr &e) override {
    for (const auto &row : e.rows) {
      row->val->accept(*this);
    }
  }

  void visitTupleExpr(const TupleExpr &e) override {
    for (const auto &exp : e.exprs) {
      exp->accept(*this);
    }
  }

  void visitSequencedExpr(const SequencedExpr &e) override {
    for (const auto &exp : e.exprs) {
      exp->accept(*this);
    }
  }

  void visitListExpr(const ListExpr &e) override {
    for (const auto &exp : e.exprs) {
      exp->accept(*this);
    }
  }

  void visitLetExpr(const LetExpr &e) override {
    for (const auto &dec : e.decls) {
      merge(vars, scope_explicit_type_variables(*dec));
    }
    for (const auto &exp : e.exprs) {
      exp->accept(*this);
    }
  }

  void visitApplicationExpr(const ApplicationExpr &e) override {
    for (const auto &exp : e.exprs) {
      exp->accept(*this);
    }
  }

  void visitCaseExpr(const CaseExpr &e) override {
    e.expr->accept(*this);
    for (const auto &c : e.cases) {
      merge(vars, scope_explicit_type_variables(*c.first));
      c.second->accept(*this);
    }
  }

  void visitFnExpr(const FnExpr &e) override {
    for (const auto &c : e.cases) {
      merge(vars, scope_explicit_type_variables(*c.first));
      c.second->accept(*this);
    }
  }

  void visitTypedExpr(const TypedExpr &e) override {
    e.expr->accept(*this);
    merge(vars, scope_explicit_type_variables(*e.type));
  }
};

ImplicitlyScopedVars scope_explicit_type_variables(const Expr &exp) {
  ExprVarScoper v;
  exp.accept(v);
  return std::move(v.vars);
}

class PatternVarScoper : public Pattern::Visitor {
 public:
  ImplicitlyScopedVars vars;

  void visitWildcardPattern(const WildcardPattern &) override {}
  void visitLiteralPattern(const LiteralPattern &) override {}
  void visitIdentifierPattern(const IdentifierPattern &) override {}
  void visitRecRowPattern(const RecRowPattern &) override {}

  void visitRecordPattern(const RecordPattern &p) override {
    for (const auto &row : p.rows) {
      row->pattern->accept(*this);
    }
  }

  void visitListPattern(const ListPattern &p) override {
    for (const auto &pat : p.patterns) {
      pat->accept(*this);
    }
  }

  void visitTuplePattern(const TuplePattern &p) override {
    for (const auto &pat : p.patterns) {
      pat->accept(*this);
    }
  }

  void visitDatatypePattern(const DatatypePattern &p) override {
    p.arg->accept(*this);
  }

  void visitLayeredPattern(const LayeredPattern &p) override {
    p.pattern->accept(*this);
  }

  void visitTypedPattern(const TypedPattern &p) override {
    p.pattern->accept(*this);
    merge(vars, scope_explicit_type_variables(*p.type));
  }
};

ImplicitlyScopedVars scope_explicit_type_variables(const Pattern &pat) {
  PatternVarScoper v;
  pat.accept(v);
  return std::move(v.vars);
}

class TypeExprVarScoper : public TypeExpr::Visitor {
 public:
  ImplicitlyScopedVars vars;

  void visitVarTypeExpr(const VarTypeExpr &t) override {
    vars[nullptr].insert(t.id);
  }

  void visitRecordTypeExpr(const RecordTypeExpr &t) override {
    for (const auto &row : t.rows) {
      row.second->accept(*this);
    }
  }

  void visitTyconTypeExpr(const TyconTypeExpr &t) override {
    for (const auto &ty : t.types) {
      ty->accept(*this);
    }
  }

  void visitTupleTypeExpr(const TupleTypeExpr &t) override {
    for (const auto &ty : t.types) {
      ty->accept(*this);
    }
  }

  void visitFuncTypeExpr(const FuncTypeExpr &t) override {
    t.param->accept(*this);
    t.ret->accept(*this);
  }
};

ImplicitlyScopedVars scope_explicit_type_variables(const TypeExpr &ty) {
  TypeExprVarScoper v;
  ty.accept(v);
  return std::move(v.vars);
}

class DeclChangeDescriber : public TDecl::Visitor {
 public:
  explicit DeclChangeDescriber(std::string &out) : out_(out) {}

  void visit(const TValDecl &decl) override {
    auto it = back_inserter(out_);
    for (const auto &b : *decl.env->val_env()->env()) {
      fmt::format_to(it, "val {} : {}\n", to_std_string(*b.first),
                     to_std_string(print_type(
                         b.second->scheme()->t(),
                         typing::CanonicalizeUndeterminedTypes::YES)));
    }
  }

 private:
  std::string &out_;
};

class TopDeclChangeDescriber : public TTopDecl::Visitor {
 public:
  std::string out;

  void visit(const TEmptyTopDecl &) override {}

  void visit(const TEndOfFileTopDecl &) override {}

  void visit(const TExprTopDecl &d) override {
    fmt::format_to(
        back_inserter(out), "val it : {}\n",
        to_std_string(typing::print_type(
            d.sigma->t(), typing::CanonicalizeUndeterminedTypes::YES)));
  }

  void visit(const TDeclTopDecl &d) override {
    DeclChangeDescriber v{out};
    d.decl->accept(v);
  }
};

}  // namespace

std::string describe_basis_updates(const TTopDecl &topdecl) {
  TopDeclChangeDescriber v;
  topdecl.accept(v);
  return std::move(v.out);
}

namespace {

void add_type(managed_ptr<typing::TypeEnv> &TE, managed_ptr<typing::ValEnv> &VE,
              managed_ptr<typing::ConstructedType> t,
              std::initializer_list<std::pair<std::u8string, typing::TypePtr>>
                  constructors = {}) {
  auto theta =
      make_managed<typing::TypeFunction>(t, to_array(t->free_variables()));
  auto type_VE = typing::ValEnv::empty();
  for (const auto &con : constructors) {
    auto &type = con.second;
    type_VE = type_VE->add_binding(con.first,
                                   make_managed<typing::TypeScheme>(
                                       type, to_array(type->free_variables())),
                                   typing::IdStatus::Constructor, false);
  }
  VE = VE + type_VE;
  TE = TE->add_binding(t->name()->name_ptr(), theta, type_VE);
}

}  // namespace

managed_ptr<typing::Basis> Typer::initial_basis() const {
  auto TE = typing::TypeEnv::empty();
  auto VE = typing::ValEnv::empty();

  add_type(TE, VE, builtins_.bigint_type());
  add_type(TE, VE, builtins_.int_type());
  add_type(TE, VE, builtins_.byte_type());
  add_type(TE, VE, builtins_.float_type());
  add_type(TE, VE, builtins_.char_type());
  add_type(TE, VE, builtins_.string_type());
  add_type(
      TE, VE, builtins_.bool_type(),
      {{u8"true", builtins_.bool_type()}, {u8"false", builtins_.bool_type()}});
  const auto a = make_managed<typing::TypeVar>(u8"'a");
  add_type(TE, VE, builtins_.list_type(a),
           {{u8"nil", builtins_.list_type(a)},
            {u8"(::)",
             make_managed<typing::FunctionType>(
                 builtins_.tuple_type(collections::make_array<typing::Type>(
                     {a, builtins_.list_type(a)})),
                 builtins_.list_type(a))}});
  add_type(TE, VE, builtins_.ref_type(a),
           {{u8"ref",
             make_managed<typing::FunctionType>(a, builtins_.ref_type(a))}});
  return make_managed<typing::Basis>(
      make_managed<typing::Env>(typing::StrEnv::empty(), TE, VE));
}

namespace {

collections::ConsPtr<ManagedString> consify(
    const std::vector<std::u8string> &names) {
  collections::ConsPtr<ManagedString> l = nullptr;
  for (const auto &n : std::ranges::reverse_view(names)) {
    l = cons(make_string(n), l);
  }
  return l;
}

managed_ptr<bigint> parse_bigint_data(const BigintLiteralData &data) {
  switch (data.base) {
    case 2:
      return parse_bigint_binary(data.number);
    case 8:
      return parse_bigint_octal(data.number);
    case 10:
      return parse_bigint_decimal(data.number);
    case 16:
      return parse_bigint_hex(data.number);
    default:
      throw std::logic_error(fmt::format("Bad bigint base: {}", data.base));
  }
}

/** Print a qualified id to string. */
std::string id_to_string(const std::vector<std::u8string> &qualifiers,
                         std::u8string_view id) {
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

managed_ptr<typing::TypeScheme> generalize_for_valbind(
    const Location &location, managed_ptr<typing::Context> C,
    typing::TypePtr type, const TExpr &expr) {
  if (expr.is_nonexpansive) {
    try {
      return typing::TypeScheme::generalize(C, type);
    } catch (typing::UnificationError &err) {
      throw ElaborationError(err, location);
    }
  }
  auto free_vars = type->free_variables() - C->free_variables();
  if (!free_vars->empty()) {
    std::string msg =
        "explicit type variables cannot be generalized at binding "
        "declaration: ";
    for (auto it = free_vars->begin(); it != free_vars->end(); ++it) {
      msg += to_std_string(**it);
      if (it != free_vars->end()) msg += ", ";
    }

    throw ElaborationError(msg, location);
  }
  return make_managed<typing::TypeScheme>(
      type, collections::make_array<ManagedString>({}));
}

typing::Substitutions compute_dummy_substitutions(Typer &typer,
                                                  managed_ptr<typing::Env> env,
                                                  const Location &location) {
  auto subs = collections::managed_map<typing::Stamp, typing::Type>({});
  std::uint64_t counter = 0;
  for (const auto &stamp : *env->undetermined_types()) {
    subs = subs->insert(stamp,
                        make_managed<typing::ConstructedType>(
                            make_managed<typing::TypeName>(
                                u8"X" + to_u8string(std::to_string(++counter)),
                                typer.new_stamp(), 0, 0),
                            collections::make_array<typing::Type>({})))
               .first;
  }
  if (!subs->empty()) {
    typer.reporter().report_warning(
        location,
        "undetermined types not generalized because of value restriction are "
        "instantiated to dummy types (X1, X2,....)");
  }
  return subs;
}

void TopDeclElaborator::visitExprTopDecl(const ExprTopDecl &node) {
  auto scopes = scope_explicit_type_variables(*node.expr);
  remove_from_children(scopes, scopes[nullptr]);
  auto vars = to_set(scopes[nullptr]);
  auto expr = typer_.elaborate(B->as_context() + vars, *node.expr, scopes);

  managed_ptr<typing::TypeScheme> sigma =
      generalize_for_valbind(node.location, B->as_context(), expr->type, *expr);
  auto env = typing::Env::empty() +
             typing::ValEnv::empty()->add_binding(
                 u8"it", sigma, typing::IdStatus::Variable, true);
  auto subs = compute_dummy_substitutions(typer_, env, node.location);
  if (!subs->empty()) {
    env = env->apply_substitutions(subs, false);
    sigma = make_managed<typing::TypeScheme>(
        typing::apply_substitutions(sigma->t(), subs,
                                    typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                    false),
        sigma->bound());
  }

  B = B + env;
  typed = std::make_unique<TExprTopDecl>(node.location, std::move(expr), sigma);
}

void TopDeclElaborator::visitDeclTopDecl(const DeclTopDecl &node) {
  auto scopes = scope_explicit_type_variables(*node.decl);
  auto r = typer_.elaborate(B->as_context(), *node.decl, scopes);
  auto subs = compute_dummy_substitutions(typer_, r.env, node.location);
  if (!subs->empty()) {
    r.decl = r.decl->apply_substitutions(subs, false);
  }
  B = B + r.decl->env;
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

class DeclElaborator : public Decl::Visitor {
 public:
  managed_ptr<typing::Env> env = typing::Env::empty();
  std::unique_ptr<TDecl> decl;
  typing::Substitutions new_substitutions =
      collections::managed_map<typing::Stamp, typing::Type>({});

  DeclElaborator(Typer &typer, managed_ptr<typing::Context> C,
                 typing::Substitutions &substitutions,
                 const ImplicitlyScopedVars &scopes)
      : typer_(typer), C(C), substitutions_(substitutions), scopes_(scopes) {}

  DECLARE_DECL_V_FUNCS;

 private:
  Typer &typer_;
  managed_ptr<typing::Context> C;
  typing::Substitutions &substitutions_;
  const ImplicitlyScopedVars &scopes_;
};

/**
 * Close a value environment that stems from the elaboration of a valbind.
 *
 * Closure is described in Section 4.8 of the Definition of Standard
 * ML (revised). Essentially, if the expression used to assign to the
 * bound variable is nonexpansive, then the type of the bound variable
 * is generalized over all the type variables and undetermined types
 * found in the type but not the enclosing context. If it is
 * expansive, then the type of the bound variable is monomorphic.
 */
managed_ptr<typing::ValEnv> close_for_valbind(managed_ptr<typing::Context> C,
                                              const match_t &match,
                                              const TExpr &expr) {
  auto closed =
      collections::managed_map<ManagedString, typing::ValueBinding>({});
  for (const auto &outcome : match.outcomes) {
    for (const auto &binding : *outcome.bindings->env()) {
      managed_ptr<typing::TypeScheme> scheme = binding.second->scheme();
      assert(scheme->bound()->empty());
      scheme = generalize_for_valbind(match.location, C, scheme->t(), expr);
      closed =
          closed
              ->insert(binding.first, make_managed<typing::ValueBinding>(
                                          scheme, typing::IdStatus::Variable))
              .first;
    }
  }
  return make_managed<typing::ValEnv>(closed);
}

void DeclElaborator::visitValDecl(const ValDecl &node) {
  std::vector<std::pair<match_t, std::unique_ptr<TExpr>>> bindings;
  bindings.reserve(node.bindings.size());
  bool is_recursive = false;
  auto type_vars = to_set(node.explicit_type_vars);
  {
    auto it = scopes_.find(&node);
    if (it != scopes_.end()) {
      type_vars = type_vars | to_set(it->second);
    }
  }
  auto duplicated_type_vars = C->explicit_type_variables() & type_vars;
  if (!duplicated_type_vars->empty()) {
    throw ElaborationError(
        fmt::format("val declaration attempts to bind variables bound by an "
                    "enclosing val declaration: {}",
                    fmt::join(*duplicated_type_vars, ", ")),
        node.location);
  }
  auto C_expr = C + type_vars;
  for (const auto &binding : node.bindings) {
    const auto &pat = binding->pat;
    auto m = typer_.elaborate_match(pat->location, C, *pat, substitutions_,
                                    typer_.new_stamp()->id());
    if (!m.new_substitutions->empty()) {
      for (auto &b : bindings) {
        b.first = b.first.apply_substitutions(m.new_substitutions, true);
      }
      C = C->apply_substitutions(m.new_substitutions);
      C_expr = C_expr->apply_substitutions(m.new_substitutions);
      new_substitutions = new_substitutions | m.new_substitutions;
    }
    if (binding->rec) is_recursive = true;
    if (is_recursive) C_expr = C_expr + m.match.outcomes.front().bindings;
    bindings.emplace_back(std::move(m.match), nullptr);
  }
  for (std::size_t i = 0; i < node.bindings.size(); ++i) {
    const auto &node_expr = node.bindings[i]->expr;
    auto &match = bindings[i].first;

    auto e =
        typer_.elaborate(C_expr, *node_expr, substitutions_,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes_);
    auto new_subs = e.new_substitutions;
    if (!new_subs->empty()) {
      match = match.apply_substitutions(new_subs, true);
    }

    typing::unification_t u;
    try {
      u = typing::unify(match.match_type, e.expr->type, substitutions_);
    } catch (typing::UnificationError &e) {
      throw ElaborationError(e, match.location);
    }
    if (!u.new_substitutions->empty()) {
      match = match.apply_substitutions(u.new_substitutions, true);
      e.expr = e.expr->apply_substitutions(u.new_substitutions, true);
      new_subs = new_subs | u.new_substitutions;
    }

    if (!new_subs->empty()) {
      for (std::size_t j = 0; j < i; ++j) {
        bindings[j].first =
            bindings[j].first.apply_substitutions(new_subs, true);
        bindings[j].second =
            bindings[j].second->apply_substitutions(new_subs, true);
      }
      for (std::size_t j = i + 1; j < bindings.size(); ++j) {
        bindings[j].first =
            bindings[j].first.apply_substitutions(new_subs, true);
      }
      C = C->apply_substitutions(new_subs);
      C_expr = C_expr->apply_substitutions(new_subs);
      new_substitutions = new_substitutions | new_subs;
    }

    env = env + close_for_valbind(C, match, *e.expr);
    bindings[i].second = std::move(e.expr);
  }
  auto unbound_variables = env->free_variables() & type_vars;
  if (!(unbound_variables->empty())) {
    throw ElaborationError(fmt::format("explicit type variable(s) cannot be "
                                       "generalized at binding declaration: {}",
                                       fmt::join(*unbound_variables, ", ")),
                           node.location);
  }
  for (const auto &b : *env->val_env()->env()) {
    typer_.reporter().report_type_judgement(
        node.location, to_std_string(*b.first), *b.second->scheme());
  }
  decl = std::make_unique<TValDecl>(node.location, std::move(bindings), env);
}

}  // namespace

Typer::elaborate_decl_t Typer::elaborate(managed_ptr<typing::Context> C,
                                         const Decl &dec,
                                         const ImplicitlyScopedVars &scopes) {
  typing::Substitutions subs =
      collections::managed_map<typing::Stamp, typing::Type>({});
  auto r = elaborate(C, dec, subs, scopes);
  return {r.env, std::move(r.decl)};
}

Typer::elaborate_decl_with_substitutions_t Typer::elaborate(
    managed_ptr<typing::Context> C, const Decl &dec,
    typing::Substitutions &substitutions, const ImplicitlyScopedVars &scopes) {
  DeclElaborator v{*this, C, substitutions, scopes};
  dec.accept(v);
  return {v.env, std::move(v.decl), v.new_substitutions};
}

namespace {

class PatternElaborator : public Pattern::Visitor {
 public:
  managed_ptr<typing::Context> C;
  typing::TypePtr type;
  pattern_t pattern = pattern_t::wildcard();
  managed_ptr<typing::ValEnv> bindings = make_managed<typing::ValEnv>(
      collections::managed_map<ManagedString, typing::ValueBinding>({}));
  bind_rule_t bind_rule;

  PatternElaborator(managed_ptr<typing::Context> C, Typer &typer)
      : C(C), typer_(typer) {}

  DECLARE_PATTERN_V_FUNCS;

 private:
  Typer &typer_;

  std::pair<std::u8string, std::optional<managed_ptr<typing::ValueBinding>>>
  lookup_val(const IdentifierPattern &pat) const;
};

void PatternElaborator::visitWildcardPattern(const WildcardPattern &) {
  type = make_managed<typing::UndeterminedType>(typer_.new_stamp());
  pattern = pattern_t::wildcard();
}

class LiteralExtractor : public Expr::Visitor {
 public:
  managed_ptr<typing::ConstructedType> type;
  std::u8string value;

  explicit LiteralExtractor(Typer &typer) : typer_(typer) {}

  void visitBigintLiteralExpr(const BigintLiteralExpr &e) override {
    type = typer_.builtins().bigint_type();
    value = parse_bigint_data(e.val)->to_string();
  }

  void visitIntLiteralExpr(const IntLiteralExpr &e) override {
    type = typer_.builtins().int_type();
    value = to_u8string(std::to_string(e.val));
  }

  void visitFpLiteralExpr(const FpLiteralExpr &e) override {
    type = typer_.builtins().float_type();
    value = to_u8string(std::to_string(e.val));
  }

  void visitStringLiteralExpr(const StringLiteralExpr &e) override {
    type = typer_.builtins().string_type();
    value = e.val;
  }

  void visitCharLiteralExpr(const CharLiteralExpr &e) override {
    type = typer_.builtins().char_type();
    value = u8"#\"";
    value += to_u8string(to_std_string(e.val));
    value += u8"\"";
  }
  void visitFstringLiteralExpr(const FstringLiteralExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitIdentifierExpr(const IdentifierExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitRecRowExpr(const RecRowExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitRecordExpr(const RecordExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitUnitExpr(const UnitExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitTupleExpr(const TupleExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitSequencedExpr(const SequencedExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitListExpr(const ListExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitLetExpr(const LetExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitApplicationExpr(const ApplicationExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitCaseExpr(const CaseExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitFnExpr(const FnExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }
  void visitTypedExpr(const TypedExpr &) override {
    throw std::logic_error("Illegal expression in literal pattern.");
  }

 private:
  Typer &typer_;
};

void PatternElaborator::visitLiteralPattern(const LiteralPattern &node) {
  LiteralExtractor v{typer_};
  node.val->accept(v);
  type = v.type;
  pattern =
      pattern_t::constructed(std::move(v.value), v.type->name(), nullptr, {});
}

class TypeNameExtractor : public typing::TypeVisitor {
 public:
  managed_ptr<typing::TypeName> name;

  void visit(const typing::TypeWithAgeRestriction &t) { t.accept(*this); }
  void visit(const typing::TypeVar &) {}
  void visit(const typing::UndeterminedType &) {}
  void visit(const typing::TupleType &) {}
  void visit(const typing::RecordType &) {}
  void visit(const typing::FunctionType &) {}
  void visit(const typing::ConstructedType &t) { name = t.name(); }
};

managed_ptr<typing::TypeName> get_type_name(typing::TypePtr type) {
  TypeNameExtractor v;
  type->accept(v);
  return v.name;
}

void PatternElaborator::visitIdentifierPattern(const IdentifierPattern &node) {
  const auto [id, binding] = lookup_val(node);
  if (!binding || (*binding)->status() == typing::IdStatus::Variable) {
    if (!node.qualifiers.empty()) {
      throw ElaborationError(
          fmt::format(
              "Variable bindings in patterns may not have qualifiers: {}",
              id_to_string(node.qualifiers, id)),
          node.location);
    }
    type = make_managed<typing::UndeterminedType>(typer_.new_stamp());
    pattern = pattern_t::wildcard();
    bindings = bindings->add_binding(
        id,
        make_managed<typing::TypeScheme>(
            type, collections::make_array<ManagedString>({})),
        typing::IdStatus::Variable, false);
    bind_rule.names.push_back(id);
  } else {
    type = (*binding)->scheme()->instantiate(typer_.stamper());
    auto name = get_type_name(type);
    if (!name) {
      throw ElaborationError("Expected value constructor taking no arguments.",
                             node.location);
    }

    pattern = pattern_t::constructed(id, name, nullptr, {});
  }
}

void PatternElaborator::visitRecRowPattern(const RecRowPattern &) {
  throw std::logic_error("Unreachable");
}

void PatternElaborator::visitRecordPattern(const RecordPattern &node) {
  typing::StringMap<typing::Type> row_types =
      collections::managed_map<ManagedString, typing::Type>({});
  std::vector<pattern_t> row_patterns;
  row_patterns.reserve(node.rows.size());
  std::vector<bind_rule_t::record_field_access_t> row_bindings;

  for (const auto &row : node.rows) {
    row->pattern->accept(*this);
    row_types = row_types->insert(make_string(row->label), type).first;
    pattern.set_field(row->label);
    row_patterns.push_back(std::move(pattern));
    if (!bind_rule.empty()) {
      row_bindings.emplace_back(row->label, std::move(bind_rule));
    }
  }

  type = make_managed<typing::RecordType>(row_types, node.has_wildcard);
  pattern = pattern_t::record(std::move(row_patterns));
  if (!row_bindings.empty()) {
    bind_rule.subtype_bindings = std::move(row_bindings);
  }
}

void PatternElaborator::visitListPattern(const ListPattern &node) {
  typing::TypePtr el_type =
      make_managed<typing::UndeterminedType>(typer_.new_stamp());
  typing::Substitutions subs =
      collections::managed_map<typing::Stamp, typing::Type>({});
  pattern_t cons_pattern =
      pattern_t::constructed(std::u8string(typing::BuiltinTypes::NIL),
                             typer_.builtins().list_name(), nullptr, {});
  bind_rule_t cons_bind_rule;

  for (const auto &pat : node.patterns | std::views::reverse) {
    pat->accept(*this);
    typing::unification_t u;
    try {
      u = typing::unify(el_type, type, subs);
    } catch (typing::UnificationError &e) {
      throw ElaborationError(e, node.location);
    }
    el_type = u.unified_type;
    std::vector<pattern_t> subpatterns;
    subpatterns.push_back(std::move(pattern));
    subpatterns.push_back(std::move(cons_pattern));
    std::vector<pattern_t> s;
    s.push_back(pattern_t::tuple(std::move(subpatterns)));
    cons_pattern = pattern_t::constructed(
        std::u8string(typing::BuiltinTypes::CONS),
        typer_.builtins().list_name(),
        typer_.builtins().tuple_type(collections::make_array<typing::Type>(
            {el_type, typer_.builtins().list_type(el_type)})),
        std::move(s));
    if (!cons_bind_rule.empty() || !bind_rule.empty()) {
      std::vector<bind_rule_t::tuple_access_t> subtype_bindings;
      if (!bind_rule.empty()) {
        subtype_bindings.emplace_back(0, std::move(bind_rule));
      }
      if (!cons_bind_rule.empty()) {
        subtype_bindings.emplace_back(1, std::move(cons_bind_rule));
      }
      cons_bind_rule.names.clear();
      cons_bind_rule.subtype_bindings = std::move(subtype_bindings);
    }
  }

  if (!subs->empty()) {
    bindings = bindings->apply_substitutions(subs, true);
    cons_pattern.apply_substitutions(subs, true);
  }
  type = typer_.builtins().list_type(el_type);
  pattern = std::move(cons_pattern);
  bind_rule = std::move(cons_bind_rule);
}

void PatternElaborator::visitTuplePattern(const TuplePattern &node) {
  std::vector<typing::TypePtr> types;
  types.reserve(node.patterns.size());
  std::vector<pattern_t> subpatterns;
  subpatterns.reserve(node.patterns.size());
  std::vector<bind_rule_t::tuple_access_t> subrules;

  for (std::size_t i = 0; i < node.patterns.size(); ++i) {
    node.patterns[i]->accept(*this);
    types.push_back(type);
    subpatterns.push_back(std::move(pattern));
    if (!bind_rule.empty()) {
      subrules.emplace_back(i, std::move(bind_rule));
    }
  }

  type = typer_.builtins().tuple_type(collections::to_array(types));
  pattern = pattern_t::tuple(std::move(subpatterns));
  if (!subrules.empty()) {
    bind_rule.subtype_bindings = std::move(subrules);
  }
}

void PatternElaborator::visitDatatypePattern(const DatatypePattern &node) {
  const auto [con_id, binding] = lookup_val(*node.constructor);
  if (!binding || (*binding)->status() == typing::IdStatus::Variable) {
    throw ElaborationError(
        fmt::format("Type constructor required but {} found instead",
                    id_to_string(node.constructor->qualifiers, con_id)),
        node.constructor->location);
  }
  auto gf =
      get_function((*binding)->scheme()->instantiate(typer_.stamper()), typer_);
  if (!gf.fn) {
    throw ElaborationError(
        fmt::format("Expected type constructor to take an argument: {}",
                    id_to_string(node.constructor->qualifiers, con_id)),
        node.constructor->location);
  }
  assert(gf.new_substitutions->empty());

  node.arg->accept(*this);

  typing::Substitutions subs =
      collections::managed_map<typing::Stamp, typing::Type>({});
  typing::unification_t u;
  try {
    u = typing::unify(gf.fn->param(), type, subs);
  } catch (typing::UnificationError &e) {
    throw ElaborationError(e, node.location);
  }
  type = gf.fn->result();
  if (!u.new_substitutions->empty()) {
    type = typing::apply_substitutions(type, u.new_substitutions);
    bindings = bindings->apply_substitutions(u.new_substitutions, true);
  }
  auto name = get_type_name(type);
  if (!name) {
    throw std::logic_error(
        "Impossible: value constructor does not produce constructed type.");
  }
  std::vector<pattern_t> s;
  s.push_back(std::move(pattern));
  pattern = pattern_t::constructed(con_id, name, u.unified_type, std::move(s));

  if (!bind_rule.empty()) {
    std::vector<bind_rule_t::tuple_access_t> r;
    r.emplace_back(0, std::move(bind_rule));
    bind_rule.subtype_bindings = std::move(r);
  }
}

void PatternElaborator::visitLayeredPattern(const LayeredPattern &node) {
  auto binding = C->env()->lookup_val({}, node.identifier);
  if (binding && (*binding)->status() != typing::IdStatus::Variable) {
    throw ElaborationError(
        fmt::format("Cannot replace binding of non-variable {} in pattern",
                    to_std_string(node.identifier)),
        node.location);
  }

  node.pattern->accept(*this);

  bindings = bindings->add_binding(
      node.identifier,
      make_managed<typing::TypeScheme>(
          type, collections::make_array<ManagedString>({})),
      typing::IdStatus::Variable, false);

  bind_rule.names.push_back(node.identifier);
}

void PatternElaborator::visitTypedPattern(const TypedPattern &node) {
  node.pattern->accept(*this);
  auto t = typer_.elaborate_type_expr(C, *node.type);
  auto subs = collections::managed_map<typing::Stamp, typing::Type>({});
  typing::unification_t u;
  try {
    u = typing::unify(type, t, subs);
  } catch (typing::UnificationError &err) {
    throw ElaborationError(err, node.location);
  }
  type = u.unified_type;
  if (!u.new_substitutions->empty()) {
    pattern.apply_substitutions(u.new_substitutions, true);
    bindings = bindings->apply_substitutions(u.new_substitutions, true);
  }
}

std::pair<std::u8string, std::optional<managed_ptr<typing::ValueBinding>>>
PatternElaborator::lookup_val(const IdentifierPattern &pat) const {
  auto id =
      typing::canonicalize_val_id(pat.identifier, pat.is_op, pat.is_prefix_op);
  auto binding = C->env()->lookup_val(pat.qualifiers, id);
  return std::make_pair(std::move(id), std::move(binding));
}

}  // namespace

std::unique_ptr<TPattern> Typer::elaborate_pattern(
    managed_ptr<typing::Context> C, const Pattern &pat) {
  PatternElaborator v{C, *this};
  pat.accept(v);
  return std::make_unique<TPattern>(pat.location, v.type, std::move(v.pattern),
                                    v.bindings, std::move(v.bind_rule));
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
                 std::uint64_t maximum_type_name_id,
                 const ImplicitlyScopedVars &scopes)
      : C(std::move(C)),
        typer_(typer),
        substitutions_(substitutions),
        maximum_type_name_id_(maximum_type_name_id),
        scopes_(scopes) {}

  DECLARE_EXPR_V_FUNCS;

 private:
  Typer &typer_;
  typing::Substitutions &substitutions_;
  std::uint64_t maximum_type_name_id_;
  const ImplicitlyScopedVars &scopes_;

  struct elaborate_rec_row_t {
    std::unique_ptr<TRecRowExpr> elaborated_row;
    typing::Substitutions new_substitutions;
  };

  elaborate_rec_row_t elaborate_rec_row(const RecRowExpr &node) const;
};

void ExprElaborator::visitBigintLiteralExpr(const BigintLiteralExpr &node) {
  typed = std::make_unique<TBigintLiteralExpr>(node.location,
                                               typer_.builtins().bigint_type(),
                                               parse_bigint_data(node.val));
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
    auto e = typer_.elaborate(C, *ns, substitutions_, maximum_type_name_id_,
                              scopes_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &ss : str_substitutions) {
        ss = ss->apply_substitutions(e.new_substitutions, true);
      }
    }
    str_substitutions.push_back(std::move(e.expr));
  }
  // TODO: Unify subexpression type with printable
  typed = std::make_unique<TFstringLiteralExpr>(
      node.location, typer_.builtins().string_type(), std::move(segments),
      std::move(str_substitutions));
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
      node.location,
      typing::apply_substitutions(
          (*val)->scheme()->instantiate(typer_.stamper()), substitutions_),
      (*val)->status(), consify(node.qualifiers), make_string(id));
}

void ExprElaborator::visitRecRowExpr(const RecRowExpr &) {
  throw std::logic_error("Unreachable.");
}

ExprElaborator::elaborate_rec_row_t ExprElaborator::elaborate_rec_row(
    const RecRowExpr &node) const {
  auto e = typer_.elaborate(C, *node.val, substitutions_, maximum_type_name_id_,
                            scopes_);
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
        expr = expr->apply_substitutions_as_rec_row(e.new_substitutions, true);
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
    auto e = typer_.elaborate(C, *ne, substitutions_, maximum_type_name_id_,
                              scopes_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions, true);
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
    auto e =
        typer_.elaborate(C, *ne, substitutions_,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions, true);
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
    auto e = typer_.elaborate(C, *ne, substitutions_, maximum_type_name_id_,
                              scopes_);
    typing::unification_t u;
    try {
      u = typing::unify(type, e.expr->type, substitutions_,
                        maximum_type_name_id_, maximum_type_name_id_);
    } catch (typing::UnificationError &e) {
      throw ElaborationError(e, node.location);
    }
    type = u.unified_type;
    if (!u.new_substitutions->empty()) {
      e.expr = e.expr->apply_substitutions(u.new_substitutions, true);
    }
    if (!u.new_substitutions->empty() || !e.new_substitutions->empty()) {
      auto new_subs = e.new_substitutions | u.new_substitutions;
      new_substitutions = new_substitutions | new_subs;
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(new_subs, true);
      }
    }
    exprs.push_back(std::move(e.expr));
  }
  typed = std::make_unique<TListExpr>(
      node.location, typer_.builtins().list_type(type), std::move(exprs));
}

void ExprElaborator::visitLetExpr(const LetExpr &node) {
  std::vector<std::unique_ptr<TDecl>> decls;
  decls.reserve(node.decls.size());
  managed_ptr<typing::Context> Cprime = C;
  for (const auto &nd : node.decls) {
    auto e = typer_.elaborate(Cprime, *nd, substitutions_, scopes_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &decl : decls) {
        decl = decl->apply_substitutions(e.new_substitutions, true);
      }
    }
    Cprime = Cprime + e.env;
    decls.push_back(std::move(e.decl));
  }

  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e =
        typer_.elaborate(Cprime, *ne, substitutions_,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes_);
    if (!e.new_substitutions->empty()) {
      new_substitutions = new_substitutions | e.new_substitutions;
      for (auto &decl : decls) {
        decl = decl->apply_substitutions(e.new_substitutions, true);
      }
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(e.new_substitutions, true);
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
      auto name = get_type_name(gf.fn->result());
      assert(name);
      return name->stamp()->id() != typer.builtins().ref_name()->stamp()->id();
    }
  }
}

void ExprElaborator::visitApplicationExpr(const ApplicationExpr &node) {
  assert(node.exprs.size() >= 2);
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  typing::TypePtr type;
  for (const auto &ne : node.exprs) {
    auto e =
        typer_.elaborate(C, *ne, substitutions_,
                         typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes_);
    auto new_subs = e.new_substitutions;
    if (exprs.empty()) {
      type = e.expr->type;
    } else {
      if (!new_subs->empty()) {
        type = typing::apply_substitutions(type, new_subs);
      }
      auto gf = get_function(type, typer_);
      if (!gf.fn) {
        throw ElaborationError(
            fmt::format("Expression must be a function but instead is {}.",
                        to_std_string(typing::print_type(exprs.back()->type))),
            exprs.back()->location);
      }
      substitutions_ = substitutions_ | gf.new_substitutions;
      if (!gf.new_substitutions->empty()) {
        e.expr = e.expr->apply_substitutions(gf.new_substitutions, true);
        new_subs = new_subs | gf.new_substitutions;
      }
      type = gf.fn->result();
      typing::unification_t u;
      try {
        u = typing::unify(gf.fn->param(), e.expr->type, substitutions_);
      } catch (typing::UnificationError &err) {
        throw ElaborationError(err, node.location);
      }
      if (!u.new_substitutions->empty()) {
        type = typing::apply_substitutions(type, u.new_substitutions);
        e.expr = e.expr->apply_substitutions(u.new_substitutions, true);
        new_subs = new_subs | u.new_substitutions;
      }
    }
    if (!new_subs->empty()) {
      for (auto &expr : exprs) {
        expr = expr->apply_substitutions(new_subs, true);
      }
      new_substitutions = new_substitutions | new_subs;
    }
    exprs.push_back(std::move(e.expr));
  }

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
  auto m = typer_.elaborate_match(node.location, C, node.cases, substitutions_,
                                  maximum_type_name_id_, scopes_);
  new_substitutions = new_substitutions | m.new_substitutions;
  auto e =
      typer_.elaborate(C, *node.expr, substitutions_,
                       typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes_);
  if (!e.new_substitutions->empty()) {
    m.match = m.match.apply_substitutions(e.new_substitutions, true);
    new_substitutions = new_substitutions | e.new_substitutions;
  }
  typing::unification_t u;
  try {
    u = typing::unify(m.match.match_type, e.expr->type, substitutions_);
  } catch (typing::UnificationError &e) {
    throw ElaborationError(e, node.location);
  }
  if (!u.new_substitutions->empty()) {
    m.match = m.match.apply_substitutions(u.new_substitutions, true);
    e.expr = e.expr->apply_substitutions(u.new_substitutions, true);
    new_substitutions = new_substitutions | u.new_substitutions;
  }
  if (m.match.result_type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in case expression (type escape).",
        node.location);
  }
  typed = std::make_unique<TCaseExpr>(node.location, std::move(e.expr),
                                      std::move(m.match));
}

void ExprElaborator::visitFnExpr(const FnExpr &node) {
  auto m = typer_.elaborate_match(node.location, C, node.cases, substitutions_,
                                  maximum_type_name_id_, scopes_);
  new_substitutions = new_substitutions | m.new_substitutions;

  if (m.match.result_type->id_of_youngest_typename() > maximum_type_name_id_ ||
      m.match.match_type->id_of_youngest_typename() > maximum_type_name_id_) {
    throw ElaborationError(
        "Illegal substitution in fn expression (type escape).", node.location);
  }
  auto type = make_managed<typing::FunctionType>(m.match.match_type,
                                                 m.match.result_type);
  typed = std::make_unique<TFnExpr>(node.location, type, std::move(m.match));
}

void ExprElaborator::visitTypedExpr(const TypedExpr &node) {
  auto t = typer_.elaborate_type_expr(C, *node.type);
  auto e = typer_.elaborate(C, *node.expr, substitutions_,
                            maximum_type_name_id_, scopes_);
  new_substitutions = new_substitutions | e.new_substitutions;
  typing::unification_t u;
  try {
    u = typing::unify(t, e.expr->type, substitutions_, maximum_type_name_id_,
                      maximum_type_name_id_);
  } catch (typing::UnificationError &e) {
    throw ElaborationError(e, node.location);
  }
  if (!u.new_substitutions->empty()) {
    e.expr = e.expr->apply_substitutions(u.new_substitutions, true);
    new_substitutions = new_substitutions | u.new_substitutions;
  }
  typed = std::move(e.expr);
}

}  // namespace

std::unique_ptr<TExpr> Typer::elaborate(managed_ptr<typing::Context> C,
                                        const Expr &exp,
                                        const ImplicitlyScopedVars &scopes) {
  typing::Substitutions s =
      collections::managed_map<typing::Stamp, typing::Type>({});
  auto e =
      elaborate(C, exp, s, typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes);
  return std::move(e.expr);
}

Typer::elaborate_expr_with_substitutions_t Typer::elaborate(
    managed_ptr<typing::Context> C, const Expr &exp,
    typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id,
    const ImplicitlyScopedVars &scopes) {
  ExprElaborator v{*this, C, substitutions, maximum_type_name_id, scopes};
  exp.accept(v);
  reporter_.report_type_judgement(exp.location, exp, *v.typed->type);
  return {std::move(v.typed), v.new_substitutions};
}

namespace {

/** A single clause of a match. */
struct clause {
  /** The not-yet-matched part of the pattern. */
  std::vector<const pattern_t *> patterns;
  /** The clause's index in the list of outcomes. */
  std::size_t outcome;
};

/** The core data structure of the match compilation. */
struct clause_matrix {
  std::vector<clause> clauses;
};

/**
 * Specialize P by constructor c (taking optional `arg_type`) at `column`.
 *
 * That is, retain the rows whose i'th pattern matches the given
 * constructor, and expand the patterns matching the arguments to the
 * constructor.
 */
clause_matrix specialize(const clause_matrix &P, std::u8string_view c,
                         typing::TypePtr arg_type, std::size_t column) {
  clause_matrix out;

  for (const auto &clause : P.clauses) {
    const auto *pat = clause.patterns[column];
    if (pat->is_wildcard() || pat->constructor() == c) {
      out.clauses.push_back(clause);
      auto &patterns = out.clauses.back().patterns;
      if (column != patterns.size() - 1) {
        patterns[column] = patterns.back();
      }
      patterns.pop_back();
      if (arg_type) {
        assert(pat->is_wildcard() || pat->subpatterns().size() == 1);
        (pat->is_wildcard() ? pat : &pat->subpatterns().front())
            ->expand(patterns, *arg_type);
      }
    }
  }

  return out;
}

/**
 * Compute default matrix of P at `column`.
 *
 * That is, retain the rows whose i'th pattern is a wildcard,
 * discarding the i'th column (actually, swapping the last with i and
 * discarding the last column).
 */
clause_matrix compute_default_matrix(const clause_matrix &P,
                                     std::size_t column) {
  clause_matrix out;
  for (const auto &clause : P.clauses) {
    const auto *pat = clause.patterns[column];
    if (pat->is_wildcard()) {
      out.clauses.push_back(clause);
      auto &patterns = out.clauses.back().patterns;
      if (column != patterns.size() - 1) {
        patterns[column] = patterns.back();
      }
      patterns.pop_back();
    }
  }
  return out;
}

using TCase = std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>;

decision_tree_t compile_tree(const clause_matrix &P, bool &failure_possible,
                             std::set<std::size_t> &useful_clauses);

dt_switch_t compile_switch(const clause_matrix &P, std::size_t i,
                           bool &failure_possible,
                           std::set<std::size_t> &useful_clauses) {
  dt_switch_t result{.index = i};
  managed_ptr<typing::TypeName> type_name;
  for (const auto &clause : P.clauses) {
    const auto *pat = clause.patterns[i];
    if (pat->is_wildcard()) continue;
    if (!type_name) type_name = pat->type_name();
    const std::u8string &con = pat->constructor();
    const auto it = result.cases.lower_bound(con);
    if (it != result.cases.cend() && it->first == con) continue;
    result.cases.emplace_hint(
        it, con,
        compile_tree(specialize(P, con, pat->arg_type(), i), failure_possible,
                     useful_clauses));
  }
  if (result.cases.size() < type_name->span()) {
    result.cases.emplace(dt_switch_t::DEFAULT_KEY,
                         compile_tree(compute_default_matrix(P, i),
                                      failure_possible, useful_clauses));
  }
  return result;
}

decision_tree_t compile_tree(const clause_matrix &P, bool &failure_possible,
                             std::set<std::size_t> &useful_clauses) {
  if (P.clauses.empty()) {
    failure_possible = true;
    return dt_fail_t{};
  }
  std::size_t i = 0;
  const auto &first_row = P.clauses.front();
  while (i < first_row.patterns.size() &&
         first_row.patterns[i]->is_wildcard()) {
    ++i;
  }
  if (i == first_row.patterns.size()) {
    useful_clauses.insert(first_row.outcome);
    return dt_leaf_t{first_row.outcome};
  }
  return compile_switch(P, i, failure_possible, useful_clauses);
}

/**
 * Compiles a pattern match into a decision tree.
 *
 * Populates the outcomes, decision_tree, and nonexhaustive fields of
 * `out`. Requires that out.location, out.match_type, and
 * out.result_type have already been initialized.
 *
 * We follow the algorithm described in Luc Maranget's 2008 paper
 * "Compiling pattern matching to good decision trees," presented at
 * the 2008 ACM SIGPLAN workshop on ML.
 */
void compile_match(match_t &match, std::vector<TCase> cases) {
  match.outcomes.reserve(cases.size());
  clause_matrix P;
  P.clauses.reserve(cases.size());
  std::size_t i = 0;
  for (auto &c : cases) {
    match.outcomes.emplace_back(
        c.first->bindings, std::move(c.first->bind_rule), std::move(c.second));
    P.clauses.emplace_back();
    c.first->pat.expand(P.clauses.back().patterns, *match.match_type);
    P.clauses.back().outcome = i++;
  }
  std::set<std::size_t> useful_clauses;

  match.decision_tree = compile_tree(P, match.nonexhaustive, useful_clauses);

  if (useful_clauses.size() != cases.size()) {
    std::size_t count = cases.size() - useful_clauses.size();
    std::size_t expected = 0;
    std::vector<std::size_t> redundant_clauses;
    for (const std::size_t c : useful_clauses) {
      while (expected++ != c) {
        --count;
        redundant_clauses.push_back(expected - 1);
      }
      if (!count) break;
    }
    throw ElaborationError(
        fmt::format("match redundant{}. Redundant clauses: {}",
                    match.nonexhaustive ? " and nonexhaustive" : "",
                    fmt::join(redundant_clauses, ", ")),
        match.location);
  }
}

template <typename It>
Typer::elaborate_match_t elaborate_match_impl(
    Typer &typer, const Location &location, managed_ptr<typing::Context> C,
    It begin, It end, typing::Substitutions &substitutions,
    std::uint64_t maximum_type_name_id, const ImplicitlyScopedVars &scopes) {
  Typer::elaborate_match_t result;

  typing::TypePtr match_type =
      make_managed<typing::UndeterminedType>(typer.new_stamp());
  typing::TypePtr result_type =
      make_managed<typing::UndeterminedType>(typer.new_stamp());
  std::vector<TCase> tcases;
  tcases.reserve(std::distance(begin, end));
  for (; begin != end; ++begin) {
    const auto &c = *begin;
    auto tpat = typer.elaborate_pattern(C, *c.first);
    typing::unification_t mu;
    try {
      mu = typing::unify(match_type, tpat->type, substitutions);
    } catch (typing::UnificationError &err) {
      throw ElaborationError(err, c.first->location);
    }
    match_type = mu.unified_type;
    auto new_subs = mu.new_substitutions;

    if (!mu.new_substitutions->empty()) {
      tpat = tpat->apply_substitutions(mu.new_substitutions, true);
    }

    auto e = typer.elaborate(C + tpat->bindings, *c.second, substitutions,
                             maximum_type_name_id, scopes);
    if (!e.new_substitutions->empty()) {
      match_type = typing::apply_substitutions(match_type, e.new_substitutions);
      tpat = tpat->apply_substitutions(e.new_substitutions, true);
      new_subs = new_subs | e.new_substitutions;
    }

    typing::unification_t ru;
    try {
      ru = typing::unify(result_type, e.expr->type, substitutions,
                         maximum_type_name_id, maximum_type_name_id);
    } catch (typing::UnificationError &err) {
      throw ElaborationError(err, c.second->location);
    }
    result_type = ru.unified_type;

    if (!ru.new_substitutions->empty()) {
      match_type =
          typing::apply_substitutions(match_type, ru.new_substitutions);
      tpat = tpat->apply_substitutions(ru.new_substitutions, true);
      e.expr = e.expr->apply_substitutions(ru.new_substitutions, true);
      new_subs = new_subs | ru.new_substitutions;
    }

    if (!new_subs->empty()) {
      for (auto &tc : tcases) {
        tc.first = tc.first->apply_substitutions(mu.new_substitutions, true);
        tc.second = tc.second->apply_substitutions(mu.new_substitutions, true);
      }
      result.new_substitutions = result.new_substitutions | new_subs;
    }

    tcases.emplace_back(std::move(tpat), std::move(e.expr));
  }

  result.match = {.location = location,
                  .match_type = match_type,
                  .result_type = result_type};
  compile_match(result.match, std::move(tcases));
  if (result.match.nonexhaustive) {
    typer.reporter().report_warning(location, "match nonexhaustive");
  }
  return result;
}

}  // namespace

Typer::elaborate_match_t Typer::elaborate_match(
    const Location &location, managed_ptr<typing::Context> C,
    const std::vector<
        std::pair<std::unique_ptr<Pattern>, std::unique_ptr<Expr>>> &cases,
    typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id,
    const ImplicitlyScopedVars &scopes) {
  return elaborate_match_impl(*this, location, C, cases.cbegin(), cases.cend(),
                              substitutions, maximum_type_name_id, scopes);
}

Typer::elaborate_match_t Typer::elaborate_match(
    const Location &location, managed_ptr<typing::Context> C,
    const Pattern &pat, typing::Substitutions &substitutions,
    std::uint64_t maximum_type_name_id) {
  auto expr = std::make_unique<UnitExpr>(location);
  std::vector<std::pair<const Pattern *, const Expr *>> cases{
      std::make_pair(&pat, &*expr)};
  return elaborate_match_impl(*this, location, C, cases.cbegin(), cases.cend(),
                              substitutions, maximum_type_name_id, {});
}

namespace {
class TypeExprElaborator : public TypeExpr::Visitor {
 public:
  typing::TypePtr type;

  TypeExprElaborator(Typer &typer, managed_ptr<typing::Context> C)
      : typer_(typer), C(C) {}

  void visitVarTypeExpr(const VarTypeExpr &node) override {
    type = make_managed<typing::TypeVar>(node.id);
  }

  void visitRecordTypeExpr(const RecordTypeExpr &node) override {
    auto rows = collections::managed_map<ManagedString, typing::Type>({});
    for (const auto &row : node.rows) {
      row.second->accept(*this);
      rows = rows->insert(make_string(row.first), type).first;
    }
    type = typer_.builtins().record_type(rows);
  }

  void visitTyconTypeExpr(const TyconTypeExpr &node) override {
    auto ty = C->env()->lookup_type(node.qualifiers, node.identifier);
    if (!ty) {
      throw ElaborationError(
          fmt::format("Unknown type constructor in type expression: {}",
                      id_to_string(node.qualifiers, node.identifier)),
          node.location);
    }
    if ((*ty)->fn()->arity() != node.types.size()) {
      throw ElaborationError(
          fmt::format("Type constructor {} takes {} type parameters but got {}",
                      id_to_string(node.qualifiers, node.identifier),
                      (*ty)->fn()->arity(), node.types.size()),
          node.location);
    }
    auto params = make_managed<collections::ManagedArray<typing::Type>>(
        node.types.size(), [&](std::size_t i) {
          node.types[i]->accept(*this);
          return type;
        });
    type = (*ty)->fn()->instantiate(params);
  }

  void visitTupleTypeExpr(const TupleTypeExpr &node) override {
    auto types = make_managed<collections::ManagedArray<typing::Type>>(
        node.types.size(), [&](std::size_t i) {
          node.types[i]->accept(*this);
          return type;
        });
    type = typer_.builtins().tuple_type(types);
  }

  void visitFuncTypeExpr(const FuncTypeExpr &node) override {
    node.param->accept(*this);
    auto param = type;
    node.ret->accept(*this);
    type = make_managed<typing::FunctionType>(param, type);
  }

 private:
  Typer &typer_;
  managed_ptr<typing::Context> C;
};

}  // namespace

typing::TypePtr Typer::elaborate_type_expr(managed_ptr<typing::Context> C,
                                           const TypeExpr &ty) {
  TypeExprElaborator v{*this, C};
  ty.accept(v);
  return v.type;
}

managed_ptr<typing::Stamp> Typer::new_stamp() { return stamp_generator_(); }

const typing::BuiltinTypes &Typer::builtins() const { return builtins_; }

}  // namespace emil
