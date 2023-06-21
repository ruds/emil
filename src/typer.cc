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
#include <cstdint>
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

namespace {

/**
 * Maps a declaration to the type variables implicitly scoped to it.
 *
 * When performing static elaboration, each type variable must be
 * associated with a val declaration. If the declaration is
 * well-formed, that type variable will be generalized away when
 * closing the value environment for that declaration.
 *
 * If a type variable is present in the optional type variable
 * sequence associated with a val declaration, then that variable is
 * *explicitly* scoped to that declaration, and may not be
 * explicitly scoped to any declaration contained within it.
 *
 * If a type variable is not explicitly scoped to any declaration,
 * then its scope must be computed. A variable is "unguarded" in a
 * declaration if it is present in that declaration but not in an
 * enclosed declaration. A variable is implicitly scoped to a
 * declaration if it is unguarded in that declaration and not
 * unguarded in any enclosing declaration.
 *
 * Some illustrative examples:
 *
 *     val id = fn (z : 'a) => z;
 * is equivalent to
 *     val 'a id = fn (z : 'a) => z;
 *
 *     val x = (let val id = fn (z : 'a) => z in id id end,
 *              fn z => z);
 * is equivalent to
 *     val x = (let val 'a id = fn (z : 'a) => z in id id end,
 *              fn y => y);
 * but
 *     val x = (let val id = fn (z : 'a) => z in id id end,
 *              fn (y: 'a) => y);
 * is equivalent to
 *     val 'a x = (let val id = fn (z : 'a) => z in id id end,
 *                 fn (y: 'a) => y);
 * and doesn't type-check. However,
 *     val x = (let val id = fn (z : 'a) => z in id id end,
 *              let val id2 = fn (y : 'a) => y in id2 end);
 * is equivalent to
 *     val x = (let val 'a id = fn (z : 'a) => z in id id end,
 *              let val 'a id2 = fn (y : 'a) => y in id2 end);
 * because the introduced `val` in the second element of the tuple guards 'a
 * from the outer declaration.
 */
using ImplicitlyScopedVars = std::map<const Decl *, std::set<std::u8string>>;

using ContextPtr = managed_ptr<typing::Context>;
}  // namespace

class TyperImpl {
 public:
  explicit TyperImpl(Reporter &reporter);

  struct elaborate_decl_t {
    managed_ptr<typing::Env> env;
    std::unique_ptr<TDecl> decl;
  };

  /** Do typing analysis of a declaration. */
  elaborate_decl_t elaborate_decl(ContextPtr C, const Decl &dec,
                                  const ImplicitlyScopedVars &scopes);

  struct elaborate_decl_with_substitutions_t {
    managed_ptr<typing::Env> env;
    std::unique_ptr<TDecl> decl;
    typing::Substitutions new_substitutions;
  };

  /** Do typing analysis of a declaration. */
  elaborate_decl_with_substitutions_t elaborate_decl(
      ContextPtr C, const Decl &dec, typing::Substitutions &substitutions,
      const ImplicitlyScopedVars &scopes);

  /** Do typing analysis of an expression. */
  std::unique_ptr<TExpr> elaborate_expr(ContextPtr C, const Expr &exp,
                                        const ImplicitlyScopedVars &scopes);

  struct elaborate_expr_with_substitutions_t {
    std::unique_ptr<TExpr> expr;
    typing::Substitutions new_substitutions;
  };

  /**
   * Do typing analysis of an expression.
   *
   * The given substitutions are applied to the expression's subtypes;
   * newly deduced substitutions are added to substitutions as well as
   * being returned separately in the result's new_substitutions
   * field.
   */
  elaborate_expr_with_substitutions_t elaborate_expr(
      ContextPtr C, const Expr &exp, typing::Substitutions &substitutions,
      std::uint64_t maximum_type_name_id, const ImplicitlyScopedVars &scopes);

  struct elaborate_match_t {
    match_t match;
    typing::Substitutions new_substitutions = typing::Substitutions::dflt();
  };

  elaborate_match_t elaborate_match(
      const Location &location, ContextPtr C,
      const std::vector<
          std::pair<std::unique_ptr<Pattern>, std::unique_ptr<Expr>>> &cases,
      typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id,
      const ImplicitlyScopedVars &scopes);

  elaborate_match_t elaborate_match(const Location &location, ContextPtr C,
                                    const Pattern &pat,
                                    typing::Substitutions &substitutions,
                                    std::uint64_t maximum_type_name_id);

  managed_ptr<typing::Type> elaborate_type_expr(ContextPtr C,
                                                const TypeExpr &ty);

  std::unique_ptr<TPattern> elaborate_pattern(ContextPtr C, const Pattern &pat);

  managed_ptr<typing::Stamp> new_stamp();
  typing::StampGenerator &stamper() { return stamp_generator_; }
  const typing::BuiltinTypes &builtins() const;

  Reporter &reporter() { return reporter_; }

  managed_ptr<typing::TypeName> type_name(std::u8string name, std::size_t arity,
                                          std::size_t span) {
    return make_managed<typing::TypeName>(name, new_stamp(), arity, span);
  }
  managed_ptr<typing::TypeName> type_name(StringPtr name, std::size_t arity,
                                          std::size_t span) {
    return make_managed<typing::TypeName>(name, new_stamp(), arity, span);
  }
  managed_ptr<typing::ConstructedType> constructed_type(
      managed_ptr<typing::TypeName> name, typing::TypeList types) {
    return make_managed<typing::ConstructedType>(name, types);
  }
  managed_ptr<typing::UndeterminedType> undetermined_type() {
    return make_managed<typing::UndeterminedType>(stamp_generator_);
  }
  typing::TypePtr ensure_age_constraint(typing::TypePtr type,
                                        std::uint64_t age) {
    return make_managed<typing::TypeWithAgeRestriction>(type, age);
  }
  typing::TypePtr tuple_type(typing::TypeList types) {
    return make_managed<typing::TupleType>(types);
  }
  typing::TypePtr record_type(typing::StringMap<typing::Type> rows) {
    return make_managed<typing::RecordType>(rows);
  }
  managed_ptr<typing::FunctionType> function_type(typing::TypePtr param,
                                                  typing::TypePtr result) {
    return make_managed<typing::FunctionType>(param, result);
  }

 private:
  friend class Typer;

  typing::StampGenerator stamp_generator_;
  typing::BuiltinTypes builtins_;
  Reporter &reporter_;
};

Typer::Typer(Reporter &reporter)
    : impl_(std::make_unique<TyperImpl>(reporter)) {}

Typer::~Typer() = default;

TyperImpl::TyperImpl(Reporter &reporter)
    : stamp_generator_(),
      builtins_(typing::BuiltinTypes::create(stamp_generator_)),
      reporter_(reporter) {}

namespace {

template <typename StringRange>
typing::StringSet to_set(const StringRange &v) {
  auto ss = typing::StringSet::dflt();
  for (const auto &s : v) {
    ss = ss->insert(make_string(s)).first;
  }
  return ss;
}

/**
 * Computes implicit scopes for explicit type variables.
 *
 * Unguarded variables are mapped to nullptr.
 */
ImplicitlyScopedVars scope_explicit_type_variables(const Decl &dec);
ImplicitlyScopedVars scope_explicit_type_variables(const Expr &exp);
ImplicitlyScopedVars scope_explicit_type_variables(const Pattern &pat);
ImplicitlyScopedVars scope_explicit_type_variables(const TypeExpr &ty);

/** Merge the ordered sequence `r` into `l`. */
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

/** Merge the values of `vars` and `new_vars` in `vars`. */
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

/** Remove all elements of `r` from `l`. */
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

/** Remove all elements of `to_remove` from each value in `vars`. */
void remove_from_children(ImplicitlyScopedVars &vars,
                          const std::set<std::u8string> to_remove) {
  for (auto &entry : vars) {
    if (!entry.first) continue;
    remove_all(entry.second, to_remove);
  }
}

/** Used to implement `scope_explicit_type_variables(const Decl&)`. */
class DeclVarScoper : public Decl::Visitor {
 public:
  ImplicitlyScopedVars vars;

  // Builds the scoping assignments from the bottom up.
  //
  // `d` guards any unguarded variables it encounters; any variable
  // scoped to `d` (implicitly or explicitly) is not scoped to any of
  // its children, so should be removed from those children's scopes.
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

  void visitDtypeDecl(const DtypeDecl &) override {}
};

ImplicitlyScopedVars scope_explicit_type_variables(const Decl &dec) {
  DeclVarScoper v;
  dec.accept(v);
  return std::move(v.vars);
}

/** Used to implement `scope_explicit_type_variables(const Expr&)`. */
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

/** Used to implement `scope_explicit_type_variables(const Pattern&)`. */
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

/** Used to implement `scope_explicit_type_variables(const TypeExpr&)`. */
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

/** Used to implement `get_function`. */
class GetFunctionVisitor : public typing::TypeVisitor {
 public:
  const typing::FunctionType *fn = nullptr;
  typing::Substitutions new_substitutions = typing::Substitutions::dflt();

  explicit GetFunctionVisitor(TyperImpl &typer) : typer_(typer) {}

  void visit(const typing::TypeWithAgeRestriction &t) override {
    t.type()->accept(*this);
  }

  void visit(const typing::UndeterminedType &t) override {
    auto p = typer_.undetermined_type();
    auto r = typer_.undetermined_type();
    auto fnptr = typer_.function_type(p, r);
    new_substitutions = new_substitutions
                            ->insert(t.stamp(), typer_.ensure_age_constraint(
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
  TyperImpl &typer_;
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
get_function_t get_function(typing::TypePtr t, TyperImpl &typer) {
  GetFunctionVisitor v{typer};
  t->accept(v);
  return {v.fn, v.new_substitutions};
}

/** Used to implement `Typer::describe_basis_updates`. */
class DeclChangeDescriber : public TDecl::Visitor {
 public:
  DeclChangeDescriber(TyperImpl &typer, std::string &out)
      : typer_(typer), out_(out) {}

  void visit(const TValDecl &decl) override {
    print_vals(*decl.env->val_env());
  }

  void visit(const TDtypeDecl &decl) override {
    print_dtypes(*decl.env->type_env());
    print_vals(*decl.env->val_env());
  }

 private:
  TyperImpl &typer_;
  std::string &out_;

  void print_vals(const typing::ValEnv &VE) {
    auto it = back_inserter(out_);
    for (const auto &b : *VE.env()) {
      fmt::format_to(it, "val {} : {}\n", to_std_string(*b.first),
                     to_std_string(print_type(
                         b.second->scheme()->t(),
                         typing::CanonicalizeUndeterminedTypes::YES)));
    }
  }

  void print_dtypes(const typing::TypeEnv &TE) {
    auto it = std::back_inserter(out_);
    for (const auto &t : *TE.env()) {
      out_ += "datatype ";
      const auto &bound = *t.second->fn()->bound();
      if (bound.size() == 1) {
        out_ += to_std_string(*bound[0]);
        out_ += " ";
      } else if (bound.size() > 1) {
        out_ += "(";
        for (std::size_t i = 0; i < bound.size(); ++i) {
          if (i) out_ += ", ";
          out_ += to_std_string(*bound[i]);
        }
        out_ += ") ";
      }
      out_ += to_std_string(*t.first);
      out_ += " = ";
      const auto &constructors = t.second->env()->env();
      for (auto cit = constructors->begin(); cit != constructors->end();
           ++cit) {
        if (cit != constructors->begin()) out_ += " | ";
        auto c_type = cit->second->scheme()->instantiate(typer_.stamper());
        auto gf = get_function(c_type, typer_);
        // If the constructor takes a parameter, we must unify the
        // result with the "canonical" type of the datatype to make
        // sure the variables match up.
        //
        // For example, take the declaration:
        //     datatype ('b, 'a) pair = Pair of ('a * 'b);
        // `pair` will be canonicalized and stored in the type environment as
        // "Λ('a, 'b).('a, 'b) pair", and `Pair` will be canonicalized and
        // stored in the value environment as "Θ('a, 'b).('a * 'b) -> ('b, 'a)
        // pair". To get everything to print correctly, we need to instantiate
        // `Pair`'s type, unify its result type with `pair`'s base type, and
        // apply the substitutions to `Pair`'s param type.
        if (gf.fn) {
          auto subs = typing::Substitutions::dflt();
          auto u = typing::unify(gf.fn->result(), t.second->fn()->t(), subs);
          auto param_type = typing::apply_substitutions(gf.fn->param(), subs);
          fmt::format_to(it, "{} of {}", cit->first,
                         to_std_string(typing::print_type(param_type)));
        } else {
          out_ += to_std_string(*cit->first);
        }
      }
      out_ += "\n";
    }
  }
};

/** Used to implement `Typer::describe_basis_updates`. */
class TopDeclChangeDescriber : public TTopDecl::Visitor {
 public:
  std::string out;

  explicit TopDeclChangeDescriber(TyperImpl &typer) : typer_(typer) {}

  void visit(const TEmptyTopDecl &) override {}

  void visit(const TEndOfFileTopDecl &) override {}

  void visit(const TDeclTopDecl &d) override {
    DeclChangeDescriber v{typer_, out};
    d.decl->accept(v);
  }

 private:
  TyperImpl &typer_;
};

}  // namespace

std::string Typer::describe_basis_updates(const TTopDecl &topdecl) {
  TopDeclChangeDescriber v{*impl_};
  topdecl.accept(v);
  return std::move(v.out);
}

namespace {

/**
 * Add a type and its constructors to TE and VE.
 *
 * Assumes that `t` and `constructors` have no stray free variables.
 */
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
  TE = TE->add_binding(t->name()->name_ptr(), theta, type_VE, false);
}

}  // namespace

managed_ptr<typing::Basis> Typer::initial_basis() const {
  auto TE = typing::TypeEnv::empty();
  auto VE = typing::ValEnv::empty();
  auto &b = impl_->builtins_;

  add_type(TE, VE, b.bigint_type());
  add_type(TE, VE, b.int_type());
  add_type(TE, VE, b.byte_type());
  add_type(TE, VE, b.float_type());
  add_type(TE, VE, b.char_type());
  add_type(TE, VE, b.string_type());
  add_type(TE, VE, b.bool_type(),
           {{u8"true", b.bool_type()}, {u8"false", b.bool_type()}});
  const auto a = make_managed<typing::TypeVar>(u8"'a");
  add_type(
      TE, VE, b.list_type(a),
      {{u8"nil", b.list_type(a)},
       {u8"(::)", make_managed<typing::FunctionType>(
                      impl_->tuple_type(collections::make_array<typing::Type>(
                          {a, b.list_type(a)})),
                      b.list_type(a))}});
  add_type(TE, VE, b.ref_type(a),
           {{u8"ref", impl_->function_type(a, b.ref_type(a))}});
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

/** Used to implement `Typer::elaborate`. */
class TopDeclElaborator : public TopDecl::Visitor {
 public:
  managed_ptr<typing::Basis> B;
  std::unique_ptr<TTopDecl> typed;

  TopDeclElaborator(TyperImpl &typer, managed_ptr<typing::Basis> B)
      : B(std::move(B)), typer_(typer) {}

  DECLARE_TOPDECL_V_FUNCS;

 private:
  TyperImpl &typer_;
};

void TopDeclElaborator::visitEmptyTopDecl(const EmptyTopDecl &node) {
  typed = std::make_unique<TEmptyTopDecl>(node.location);
}

void TopDeclElaborator::visitEndOfFileTopDecl(const EndOfFileTopDecl &node) {
  typed = std::make_unique<TEndOfFileTopDecl>(node.location);
}

/**
 * Create a new dummy type to substitute for any undetermined type not
 * generalized.
 *
 * This prevents unsound substitutions prevented by the value restriction.
 */
typing::Substitutions compute_dummy_substitutions(TyperImpl &typer,
                                                  managed_ptr<typing::Env> env,
                                                  const Location &location) {
  auto subs = typing::Substitutions::dflt();
  std::uint64_t counter = 0;
  for (const auto &stamp : *env->undetermined_types()) {
    subs =
        subs->insert(
                stamp,
                typer.constructed_type(
                    typer.type_name(
                        u8"X" + to_u8string(std::to_string(++counter)), 0, 0),
                    typing::TypeList::dflt()))
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

void TopDeclElaborator::visitDeclTopDecl(const DeclTopDecl &node) {
  auto scopes = scope_explicit_type_variables(*node.decl);
  auto r = typer_.elaborate_decl(B->as_context(), *node.decl, scopes);
  auto subs = compute_dummy_substitutions(typer_, r.env, node.location);
  if (!subs->empty()) {
    r.decl = r.decl->apply_substitutions(subs, false);
  }
  B = B + r.decl->env;

  typed = std::make_unique<TDeclTopDecl>(node.location, std::move(r.decl));
}

}  // namespace

Typer::elaborate_t Typer::elaborate(managed_ptr<typing::Basis> B,
                                    const TopDecl &topdec) {
  TopDeclElaborator v(*impl_, std::move(B));
  topdec.accept(v);
  return {std::move(v.B), std::move(v.typed)};
}

namespace {

/** Used to implement `TyperImpl::elaborate_decl`. */
class DeclElaborator : public Decl::Visitor {
 public:
  managed_ptr<typing::Env> env = typing::Env::empty();
  std::unique_ptr<TDecl> decl;
  typing::Substitutions new_substitutions = typing::Substitutions::dflt();

  DeclElaborator(TyperImpl &typer, ContextPtr C,
                 typing::Substitutions &substitutions,
                 const ImplicitlyScopedVars &scopes)
      : typer_(typer), C(C), substitutions_(substitutions), scopes_(scopes) {}

  DECLARE_DECL_V_FUNCS;

 private:
  TyperImpl &typer_;
  ContextPtr C;
  typing::Substitutions &substitutions_;
  const ImplicitlyScopedVars &scopes_;
};

/**
 * Close `type` for `valbind` in the context of `C`.
 *
 * @see `close_for_valbind`.
 */
managed_ptr<typing::TypeScheme> generalize_for_valbind(const Location &location,
                                                       ContextPtr C,
                                                       typing::TypePtr type,
                                                       const TExpr &expr) {
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
managed_ptr<typing::ValEnv> close_for_valbind(ContextPtr C,
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

/** Get all the type variables properly scoped to this decl. */
typing::StringSet get_scoped_type_vars(ContextPtr C,
                                       const ImplicitlyScopedVars &scopes,
                                       const ValDecl &node) {
  auto type_vars = to_set(node.explicit_type_vars);
  {
    const auto it = scopes.find(&node);
    if (it != scopes.end()) {
      type_vars = type_vars | to_set(it->second);
    }
  }
  const auto duplicated_type_vars = C->explicit_type_variables() & type_vars;
  if (!duplicated_type_vars->empty()) {
    throw ElaborationError(
        fmt::format("val declaration attempts to bind variables bound by an "
                    "enclosing val declaration: {}",
                    fmt::join(*duplicated_type_vars, ", ")),
        node.location);
  }
  return type_vars;
}

using val_bind_bindings =
    std::vector<std::pair<match_t, std::unique_ptr<TExpr>>>;

struct elaborate_val_bind_patterns_t {
  /** Context to be used to elaborate assignment expressions. */
  ContextPtr C_expr;
  /** The elaborated matches, each associated with nullptr. */
  val_bind_bindings bindings;
  typing::Substitutions new_substitutions = typing::Substitutions::dflt();
};

/**
 * Elaborate the patterns found in a ValDecl.
 *
 * A ValDecl comprises zero or more ValBinds. Each ValBind contains a
 * pattern and an expression that it is matched against. We start by
 * elaborating all the patterns, developing a context as necessary for
 * use when elaborating the expressions.
 */
elaborate_val_bind_patterns_t elaborate_val_bind_patterns(
    TyperImpl &typer, typing::Substitutions &substitutions, ContextPtr C,
    typing::StringSet type_vars, const ValDecl &node) {
  elaborate_val_bind_patterns_t result;
  result.bindings.reserve(node.bindings.size());
  result.C_expr = C + type_vars;

  bool is_recursive = false;
  for (const auto &binding : node.bindings) {
    const auto &pat = binding->pat;
    TyperImpl::elaborate_match_t m;
    try {
      // Any undetermined types introduced in elaborating the pattern
      // must not be substituted by a type introduced in later
      // elaboration; hence create a new stamp and make it the maximum
      // allowable type id.
      m = typer.elaborate_match(pat->location, C, *pat, substitutions,
                                typer.new_stamp()->id());
    } catch (typing::BindingError &err) {
      throw ElaborationError(
          fmt::format("Bound identifier {} multiple times in val declaration",
                      to_std_string(err.id)),
          pat->location);
    }
    if (!m.new_substitutions->empty()) {
      for (auto &b : result.bindings) {
        b.first = b.first.apply_substitutions(m.new_substitutions, true);
      }
      result.new_substitutions = result.new_substitutions | m.new_substitutions;
    }
    if (binding->rec) is_recursive = true;
    if (is_recursive)
      result.C_expr = result.C_expr + m.match.outcomes.front().bindings;
    result.bindings.emplace_back(std::move(m.match), nullptr);
  }
  return result;
}

/**
 * Elaborate the expressions found in a ValDecl.
 *
 * We continue by elaborating each expression and unifying its type
 * with the corresponding pattern's type.
 *
 * Returns the new substitutions deduced herein.
 */
typing::Substitutions elaborate_val_bind_exprs(
    TyperImpl &typer, typing::Substitutions &substitutions,
    const ImplicitlyScopedVars &scopes, ContextPtr C_expr,
    val_bind_bindings &bindings, const ValDecl &node) {
  auto new_substitutions = typing::Substitutions::dflt();
  for (std::size_t i = 0; i < node.bindings.size(); ++i) {
    const auto &node_expr = node.bindings[i]->expr;
    auto &match = bindings[i].first;

    auto e = typer.elaborate_expr(C_expr, *node_expr, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  scopes);
    auto new_subs = e.new_substitutions;
    if (!new_subs->empty()) {
      match = match.apply_substitutions(new_subs, true);
    }

    typing::unification_t u;
    try {
      u = typing::unify(match.match_type, e.expr->type, substitutions);
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
      new_substitutions = new_substitutions | new_subs;
    }
    bindings[i].second = std::move(e.expr);
  }
  return new_substitutions;
}

/**
 * Given the bindings, compute the environment they produce.
 *
 * Closes types as appropriate. Checks that all of the type variables
 * scoped to this declaration are generalized away.
 */
managed_ptr<typing::Env> compute_val_decl_env(
    const Location &location, ContextPtr C, const val_bind_bindings &bindings,
    typing::StringSet scoped_type_vars) {
  auto env = typing::Env::empty();
  for (const auto &b : bindings) {
    auto VE = close_for_valbind(C, b.first, *b.second);
    auto overlap = env->val_env()->env() & VE->env();
    if (!overlap->empty()) {
      throw ElaborationError(
          fmt::format("Separate clauses of a val declaration bound the same "
                      "identifier(s): {}",
                      fmt::join(*overlap | std::views::keys, ", ")),
          location);
    }
    env = env + VE;
  }
  auto unbound_variables = env->free_variables() & scoped_type_vars;
  if (!(unbound_variables->empty())) {
    throw ElaborationError(fmt::format("explicit type variable(s) cannot be "
                                       "generalized at binding declaration: {}",
                                       fmt::join(*unbound_variables, ", ")),
                           location);
  }
  return env;
}

void DeclElaborator::visitValDecl(const ValDecl &node) {
  const auto type_vars = get_scoped_type_vars(C, scopes_, node);
  auto pats =
      elaborate_val_bind_patterns(typer_, substitutions_, C, type_vars, node);
  auto new_subs = pats.new_substitutions |
                  elaborate_val_bind_exprs(typer_, substitutions_, scopes_,
                                           pats.C_expr, pats.bindings, node);
  if (!new_subs->empty()) {
    C = C->apply_substitutions(new_subs);
    new_substitutions = new_substitutions | new_subs;
  }
  env = compute_val_decl_env(node.location, C, pats.bindings, type_vars);
  for (const auto &b : *env->val_env()->env()) {
    typer_.reporter().report_type_judgement(
        node.location, to_std_string(*b.first), *b.second->scheme());
  }
  decl =
      std::make_unique<TValDecl>(node.location, std::move(pats.bindings), env);
}

/**
 * "Seed" the type environment for a datatype binding.
 *
 * Datatype bindings are potentially (mutually) recursive, so we need
 * to start our elaboration by adding a binding for each type defined
 * in a datatype declaration. The bindings have correct (though not
 * necessarily canonical) type function and empty value environments
 * (ie the constructors are not present). (The type function is
 * noncanonical in that it uses the type variables indicated in the
 * source instead of 'a, 'b, 'c, ...).
 */
managed_ptr<typing::TypeEnv> seed_type_env(
    TyperImpl &typer, const std::vector<std::unique_ptr<DtypeBind>> &bindings) {
  auto TE = typing::TypeEnv::empty();
  for (const auto &db : bindings) {
    auto name = make_string(db->identifier);
    auto type_var_names =
        make_managed<collections::ManagedArray<ManagedString>>(
            db->types.size(),
            [&](const std::size_t i) { return make_string(db->types[i]); });
    auto type_vars = make_managed<collections::ManagedArray<typing::Type>>(
        type_var_names->size(), [&](const std::size_t i) {
          return make_managed<typing::TypeVar>((*type_var_names)[i]);
        });
    try {
      TE = TE->add_binding(
          name,
          make_managed<typing::TypeFunction>(
              typer.constructed_type(typer.type_name(name, db->types.size(),
                                                     db->constructors.size()),
                                     type_vars),
              type_var_names),
          typing::ValEnv::empty(), false);
    } catch (typing::BindingError &err) {
      throw ElaborationError(
          fmt::format(
              "Datatype declaration bound type identifier multiple times: {}",
              to_std_string(err.id)),
          db->location);
    }
  }
  return TE;
}

/**
 * Returns the first subtype of a tuple type.
 *
 * Requires that the type being visited actually is a tuple.
 */
class Tuple0Extractor : public typing::TypeVisitor {
 public:
  typing::TypePtr type;

  void visit(const typing::TupleType &t) override {
    if (t.types()->empty()) throw std::logic_error("ugh");
    type = (*t.types())[0];
  }

  void visit(const typing::TypeWithAgeRestriction &) override {
    throw std::logic_error("ugh");
  }
  void visit(const typing::TypeVar &) override {
    throw std::logic_error("ugh");
  }
  void visit(const typing::UndeterminedType &) override {
    throw std::logic_error("ugh");
  }
  void visit(const typing::RecordType &) override {
    throw std::logic_error("ugh");
  }
  void visit(const typing::FunctionType &) override {
    throw std::logic_error("ugh");
  }
  void visit(const typing::ConstructedType &) override {
    throw std::logic_error("ugh");
  }
};

struct elaborate_dtype_bind_t {
  managed_ptr<typing::TypeEnv> TE = typing::TypeEnv::empty();
  managed_ptr<typing::ValEnv> VE = typing::ValEnv::empty();
};

/** Elaborate a single DtypeBind. */
elaborate_dtype_bind_t elaborate_dtype_bind(TyperImpl &typer, ContextPtr C,
                                            const DtypeBind &binding) {
  elaborate_dtype_bind_t r;
  const auto theta = (*C->env()->lookup_type({}, binding.identifier))->fn();
  const auto type = theta->t();
  const auto bound_set = collections::to_set(theta->bound());
  std::vector<typing::TypePtr> params;
  params.push_back(type);
  for (const auto &con : binding.constructors) {
    const auto id =
        canonicalize_val_id(con->identifier, con->is_op, con->is_prefix_op);
    typing::TypePtr con_type = type;
    if (con->param) {
      auto param_type = typer.elaborate_type_expr(C, *con->param);
      auto extra_vars = param_type->free_variables() - bound_set;
      if (!extra_vars->empty()) {
        throw ElaborationError(
            fmt::format("Value constructor uses type variable(s) not bound in "
                        "datatype declaration: {}",
                        fmt::join(*extra_vars, ", ")),
            con->location);
      }
      params.push_back(param_type);
      con_type = make_managed<typing::FunctionType>(param_type, type);
    }
    try {
      r.VE = r.VE->add_binding(id, typing::TypeScheme::generalize(C, con_type),
                               typing::IdStatus::Constructor, false);
    } catch (typing::BindingError &err) {
      throw ElaborationError(fmt::format("Datatype declaration bound value "
                                         "constructor multiple times: {}",
                                         to_std_string(err.id)),
                             con->location);
    }
  }

  auto g = typing::TypeScheme::generalize(C, type);
  assert(g->undetermined_types()->empty() && g->free_variables()->empty());
  r.TE = r.TE->add_binding(
      make_string(binding.identifier),
      make_managed<typing::TypeFunction>(g->t(), g->bound()), r.VE, false);
  return r;
}

void DeclElaborator::visitDtypeDecl(const DtypeDecl &node) {
  auto C_seed = C + seed_type_env(typer_, node.bindings);
  auto VE = typing::ValEnv::empty();
  auto TE = typing::TypeEnv::empty();
  for (const auto &binding : node.bindings) {
    auto r = elaborate_dtype_bind(typer_, C_seed, *binding);
    VE = VE + r.VE;
    TE = TE + r.TE;
  }
  env = env + make_managed<typing::Env>(typing::StrEnv::empty(), TE, VE);
  decl = std::make_unique<TDtypeDecl>(node.location, env);
}

}  // namespace

TyperImpl::elaborate_decl_t TyperImpl::elaborate_decl(
    ContextPtr C, const Decl &dec, const ImplicitlyScopedVars &scopes) {
  typing::Substitutions subs =
      collections::managed_map<typing::Stamp, typing::Type>({});
  auto r = elaborate_decl(C, dec, subs, scopes);
  return {r.env, std::move(r.decl)};
}

TyperImpl::elaborate_decl_with_substitutions_t TyperImpl::elaborate_decl(
    ContextPtr C, const Decl &dec, typing::Substitutions &substitutions,
    const ImplicitlyScopedVars &scopes) {
  DeclElaborator v{*this, C, substitutions, scopes};
  dec.accept(v);
  return {v.env, std::move(v.decl), v.new_substitutions};
}

namespace {

/** Used to implement `TyperImpl::elaborate_pattern`. */
class PatternElaborator : public Pattern::Visitor {
 public:
  ContextPtr C;
  typing::TypePtr type;
  pattern_t pattern = pattern_t::wildcard();
  managed_ptr<typing::ValEnv> bindings = make_managed<typing::ValEnv>(
      collections::managed_map<ManagedString, typing::ValueBinding>({}));
  bind_rule_t bind_rule;

  PatternElaborator(ContextPtr C, TyperImpl &typer) : C(C), typer_(typer) {}

  DECLARE_PATTERN_V_FUNCS;

 private:
  TyperImpl &typer_;

  std::pair<std::u8string, std::optional<managed_ptr<typing::ValueBinding>>>
  lookup_val(const IdentifierPattern &pat) const;
};

void PatternElaborator::visitWildcardPattern(const WildcardPattern &) {
  type = make_managed<typing::UndeterminedType>(typer_.new_stamp());
  pattern = pattern_t::wildcard();
}

/** Extract the specific literal from a literal pattern. */
class LiteralExtractor : public Expr::Visitor {
 public:
  /** The type of the literal. */
  managed_ptr<typing::ConstructedType> type;
  /** A string representation of the value of the literal. */
  std::u8string value;

  explicit LiteralExtractor(TyperImpl &typer) : typer_(typer) {}

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
  TyperImpl &typer_;
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
    type = typer_.undetermined_type();
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
  typing::TypePtr el_type = typer_.undetermined_type();
  auto subs = typing::Substitutions::dflt();
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
        typer_.tuple_type(collections::make_array<typing::Type>(
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

  type = typer_.tuple_type(collections::to_array(types));
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
  auto id = canonicalize_val_id(pat.identifier, pat.is_op, pat.is_prefix_op);
  auto binding = C->env()->lookup_val(pat.qualifiers, id);
  return std::make_pair(std::move(id), std::move(binding));
}

}  // namespace

std::unique_ptr<TPattern> TyperImpl::elaborate_pattern(ContextPtr C,
                                                       const Pattern &pat) {
  PatternElaborator v{C, *this};
  pat.accept(v);
  return std::make_unique<TPattern>(pat.location, v.type, std::move(v.pattern),
                                    v.bindings, std::move(v.bind_rule));
}

namespace {

/** Used to implement `TyperImpl::elaborate_expr`. */
class ExprElaborator : public Expr::Visitor {
 public:
  const ContextPtr C;
  std::unique_ptr<TExpr> typed;
  typing::Substitutions new_substitutions =
      collections::managed_map<typing::Stamp, typing::Type>({});

  ExprElaborator(TyperImpl &typer, ContextPtr C,
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
  TyperImpl &typer_;
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
    auto e = typer_.elaborate_expr(C, *ns, substitutions_,
                                   maximum_type_name_id_, scopes_);
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
  const auto id =
      canonicalize_val_id(node.identifier, node.is_op, node.is_prefix_op);
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
  auto e = typer_.elaborate_expr(C, *node.val, substitutions_,
                                 maximum_type_name_id_, scopes_);
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
  typed = std::make_unique<TRecordExpr>(node.location, typer_.record_type(rows),
                                        std::move(exprs));
}

void ExprElaborator::visitUnitExpr(const UnitExpr &node) {
  typed = std::make_unique<TTupleExpr>(
      node.location,
      typer_.tuple_type(collections::make_array<typing::Type>({})),
      std::vector<std::unique_ptr<TExpr>>{});
}

void ExprElaborator::visitTupleExpr(const TupleExpr &node) {
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate_expr(C, *ne, substitutions_,
                                   maximum_type_name_id_, scopes_);
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
  typed = std::make_unique<TTupleExpr>(node.location, typer_.tuple_type(types),
                                       std::move(exprs));
}

void ExprElaborator::visitSequencedExpr(const SequencedExpr &node) {
  std::vector<std::unique_ptr<TExpr>> exprs;
  exprs.reserve(node.exprs.size());
  for (const auto &ne : node.exprs) {
    auto e = typer_.elaborate_expr(C, *ne, substitutions_,
                                   typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                   scopes_);
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
    auto e = typer_.elaborate_expr(C, *ne, substitutions_,
                                   maximum_type_name_id_, scopes_);
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
  ContextPtr Cprime = C;
  for (const auto &nd : node.decls) {
    auto e = typer_.elaborate_decl(Cprime, *nd, substitutions_, scopes_);
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
    auto e = typer_.elaborate_expr(Cprime, *ne, substitutions_,
                                   typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                   scopes_);
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

/** Used to implement `get_identifier`. */
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

/**
 * Determines whether a function application is nonexpansive.
 *
 * See Section 4.7 of The Definition of Standard ML (Revised).
 */
bool is_nonexpansive_application(
    const std::vector<std::unique_ptr<TExpr>> &exprs, TyperImpl &typer) {
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
    auto e = typer_.elaborate_expr(C, *ne, substitutions_,
                                   typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                   scopes_);
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
  auto e = typer_.elaborate_expr(C, *node.expr, substitutions_,
                                 typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                 scopes_);
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
  auto e = typer_.elaborate_expr(C, *node.expr, substitutions_,
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

std::unique_ptr<TExpr> TyperImpl::elaborate_expr(
    ContextPtr C, const Expr &exp, const ImplicitlyScopedVars &scopes) {
  typing::Substitutions s =
      collections::managed_map<typing::Stamp, typing::Type>({});
  auto e = elaborate_expr(C, exp, s,
                          typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, scopes);
  return std::move(e.expr);
}

TyperImpl::elaborate_expr_with_substitutions_t TyperImpl::elaborate_expr(
    ContextPtr C, const Expr &exp, typing::Substitutions &substitutions,
    std::uint64_t maximum_type_name_id, const ImplicitlyScopedVars &scopes) {
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

struct elaborate_cases_t {
  typing::TypePtr match_type;
  typing::TypePtr result_type;
  std::vector<TCase> tcases;
  typing::Substitutions new_substitutions = typing::Substitutions::dflt();
};

/**
 * Elaborate the cases of a match.
 *
 * Each case of a match comprises a pattern to match against and an
 * expression to evaluate to. The types of all of the patterns must be
 * unified, and the types of all the expressions must separately be
 * unified.
 */
template <typename It>
elaborate_cases_t elaborate_cases(TyperImpl &typer, ContextPtr C, It begin,
                                  It end, typing::Substitutions &substitutions,
                                  std::uint64_t maximum_type_name_id,
                                  const ImplicitlyScopedVars &scopes) {
  elaborate_cases_t result;
  result.match_type = typer.undetermined_type();
  result.result_type = typer.undetermined_type();
  result.tcases.reserve(std::distance(begin, end));
  for (; begin != end; ++begin) {
    const auto &c = *begin;
    auto tpat = typer.elaborate_pattern(C, *c.first);
    typing::unification_t mu;
    try {
      mu = typing::unify(result.match_type, tpat->type, substitutions);
    } catch (typing::UnificationError &err) {
      throw ElaborationError(err, c.first->location);
    }
    result.match_type = mu.unified_type;
    auto new_subs = mu.new_substitutions;

    if (!mu.new_substitutions->empty()) {
      tpat = tpat->apply_substitutions(mu.new_substitutions, true);
    }

    // The expression is evaluated in a context that includes the
    // bindings introduced by the pattern we just matched against.
    auto e = typer.elaborate_expr(C + tpat->bindings, *c.second, substitutions,
                                  maximum_type_name_id, scopes);
    if (!e.new_substitutions->empty()) {
      result.match_type =
          typing::apply_substitutions(result.match_type, e.new_substitutions);
      tpat = tpat->apply_substitutions(e.new_substitutions, true);
      new_subs = new_subs | e.new_substitutions;
    }

    typing::unification_t ru;
    try {
      ru = typing::unify(result.result_type, e.expr->type, substitutions,
                         maximum_type_name_id, maximum_type_name_id);
    } catch (typing::UnificationError &err) {
      throw ElaborationError(err, c.second->location);
    }
    result.result_type = ru.unified_type;

    if (!ru.new_substitutions->empty()) {
      result.match_type =
          typing::apply_substitutions(result.match_type, ru.new_substitutions);
      tpat = tpat->apply_substitutions(ru.new_substitutions, true);
      e.expr = e.expr->apply_substitutions(ru.new_substitutions, true);
      new_subs = new_subs | ru.new_substitutions;
    }

    if (!new_subs->empty()) {
      for (auto &tc : result.tcases) {
        tc.first = tc.first->apply_substitutions(mu.new_substitutions, true);
        tc.second = tc.second->apply_substitutions(mu.new_substitutions, true);
      }
      result.new_substitutions = result.new_substitutions | new_subs;
    }

    result.tcases.emplace_back(std::move(tpat), std::move(e.expr));
  }
  return result;
}

template <typename It>
TyperImpl::elaborate_match_t elaborate_match_impl(
    TyperImpl &typer, const Location &location, ContextPtr C, It begin, It end,
    typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id,
    const ImplicitlyScopedVars &scopes) {
  TyperImpl::elaborate_match_t result;
  auto cases = elaborate_cases(typer, C, begin, end, substitutions,
                               maximum_type_name_id, scopes);
  result.new_substitutions = cases.new_substitutions;

  result.match = {.location = location,
                  .match_type = cases.match_type,
                  .result_type = cases.result_type};
  compile_match(result.match, std::move(cases.tcases));
  if (result.match.nonexhaustive) {
    typer.reporter().report_warning(location, "match nonexhaustive");
  }
  return result;
}

}  // namespace

TyperImpl::elaborate_match_t TyperImpl::elaborate_match(
    const Location &location, ContextPtr C,
    const std::vector<
        std::pair<std::unique_ptr<Pattern>, std::unique_ptr<Expr>>> &cases,
    typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id,
    const ImplicitlyScopedVars &scopes) {
  return elaborate_match_impl(*this, location, C, cases.cbegin(), cases.cend(),
                              substitutions, maximum_type_name_id, scopes);
}

TyperImpl::elaborate_match_t TyperImpl::elaborate_match(
    const Location &location, ContextPtr C, const Pattern &pat,
    typing::Substitutions &substitutions, std::uint64_t maximum_type_name_id) {
  auto expr = std::make_unique<UnitExpr>(location);
  std::vector<std::pair<const Pattern *, const Expr *>> cases{
      std::make_pair(&pat, &*expr)};
  return elaborate_match_impl(*this, location, C, cases.cbegin(), cases.cend(),
                              substitutions, maximum_type_name_id, {});
}

namespace {

/** Used to implement `TyperImpl::elaborate_type_expr`. */
class TypeExprElaborator : public TypeExpr::Visitor {
 public:
  typing::TypePtr type;

  TypeExprElaborator(TyperImpl &typer, ContextPtr C) : typer_(typer), C(C) {}

  void visitVarTypeExpr(const VarTypeExpr &node) override {
    type = make_managed<typing::TypeVar>(node.id);
  }

  void visitRecordTypeExpr(const RecordTypeExpr &node) override {
    auto rows = collections::managed_map<ManagedString, typing::Type>({});
    for (const auto &row : node.rows) {
      row.second->accept(*this);
      rows = rows->insert(make_string(row.first), type).first;
    }
    type = typer_.record_type(rows);
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
    type = typer_.tuple_type(types);
  }

  void visitFuncTypeExpr(const FuncTypeExpr &node) override {
    node.param->accept(*this);
    auto param = type;
    node.ret->accept(*this);
    type = make_managed<typing::FunctionType>(param, type);
  }

 private:
  TyperImpl &typer_;
  ContextPtr C;
};

}  // namespace

typing::TypePtr TyperImpl::elaborate_type_expr(ContextPtr C,
                                               const TypeExpr &ty) {
  TypeExprElaborator v{*this, C};
  ty.accept(v);
  return v.type;
}

managed_ptr<typing::Stamp> TyperImpl::new_stamp() { return stamp_generator_(); }

const typing::BuiltinTypes &TyperImpl::builtins() const { return builtins_; }

}  // namespace emil
