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

#include "emil/typed_ast.h"

#include <algorithm>
#include <cassert>
#include <compare>
#include <stdexcept>
#include <utility>
#include <variant>

#include "emil/bigint.h"  // IWYU pragma: keep
#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/tree.h"
#include "emil/types.h"

namespace emil {

pattern_t::pattern_t(repr r) : repr_(std::move(r)) {}

managed_ptr<pattern_t> pattern_t::wildcard() {
  return make_managed<pattern_t>(wildcard_t{});
}

managed_ptr<pattern_t> pattern_t::constructed(
    StringPtr constructor, managed_ptr<typing::TypeName> type_name,
    typing::TypePtr arg_type, collections::ArrayPtr<pattern_t> subpatterns) {
  assert(constructor && !constructor->empty());
  assert(type_name);
  assert(subpatterns);
  return make_managed<pattern_t>(
      constructed_t{constructor, type_name, arg_type, subpatterns});
}

managed_ptr<pattern_t> pattern_t::tuple(
    collections::ArrayPtr<pattern_t> subpatterns) {
  assert(subpatterns);
  return make_managed<pattern_t>(tuple_t{subpatterns});
}

managed_ptr<pattern_t> pattern_t::record(
    collections::ArrayPtr<pattern_t> subpatterns) {
  assert(subpatterns);
  assert(std::is_sorted(
      subpatterns->begin(), subpatterns->end(),
      [](const auto& l, const auto& r) { return *l->field() < *r->field(); }));
  return make_managed<pattern_t>(record_t{subpatterns});
}

bool pattern_t::is_wildcard() const {
  return std::holds_alternative<wildcard_t>(repr_);
}

bool pattern_t::is_tuple() const {
  return std::holds_alternative<tuple_t>(repr_);
}

bool pattern_t::is_record() const {
  return std::holds_alternative<record_t>(repr_);
}

bool pattern_t::is_record_field() const { return static_cast<bool>(field_); }

bool pattern_t::is_constructed() const {
  return std::holds_alternative<constructed_t>(repr_);
}

StringPtr pattern_t::constructor() const {
  assert(is_constructed());
  return get<constructed_t>(repr_).constructor;
}

managed_ptr<typing::TypeName> pattern_t::type_name() const {
  assert(is_constructed());
  return get<constructed_t>(repr_).type_name;
}

typing::TypePtr pattern_t::arg_type() const {
  assert(is_constructed());
  return get<constructed_t>(repr_).arg_type;
}

namespace {

template <typename... Ts>
struct overloaded : Ts... {
  using Ts::operator()...;
};

template <typename... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

}  // namespace

collections::ArrayPtr<pattern_t> pattern_t::subpatterns() const {
  assert(!is_wildcard());
  return std::visit(
      overloaded{[](wildcard_t) -> collections::ArrayPtr<pattern_t> {
                   throw std::invalid_argument(
                       "May not call subpatterns() on wildcard pattern.");
                 },
                 [](const auto& r) { return r.subpatterns; }},
      repr_);
}

StringPtr pattern_t::field() const {
  assert(is_record_field());
  return field_;
}

void pattern_t::set_field(StringPtr field) { field_ = field; }

namespace {

class PatternExpander : public typing::TypeVisitor {
 public:
  PatternExpander(managed_ptr<pattern_t> pat,
                  std::vector<managed_ptr<pattern_t>>& out)
      : pat_(pat), out_(out) {}

  void visit(const typing::TypeWithAgeRestriction& t) override {
    t.type()->accept(*this);
  }

  void visit(const typing::TypeVar&) override { assert(pat_->is_wildcard()); }

  void visit(const typing::UndeterminedType&) override {
    assert(pat_->is_wildcard());
  }

  void visit(const typing::TupleType& t) override {
    if (pat_->is_wildcard()) {
      for (const auto& subtype : *t.types()) {
        subtype->accept(*this);
      }
    } else {
      const auto& subpatterns = pat_->subpatterns();
      assert(subpatterns->size() == t.types()->size());
      for (std::size_t i = 0; i < subpatterns->size(); ++i) {
        pat_ = (*subpatterns)[i];
        (*t.types())[i]->accept(*this);
      }
    }
  }

  void visit(const typing::RecordType& t) override {
    if (pat_->is_wildcard()) {
      for (const auto& row : *t.rows()) {
        row.second->accept(*this);
      }
    } else {
      auto it = pat_->subpatterns()->begin();
      const auto end = pat_->subpatterns()->end();
      for (const auto& row : *t.rows()) {
        if (it == end || *row.first < *(*it)->field()) {
          pat_ = pattern_t::wildcard();
        } else {
          assert(*row.first == *(*it)->field());
          pat_ = *it++;
        }
        row.second->accept(*this);
      }
    }
  }

  void visit(const typing::FunctionType&) override {
    assert(pat_->is_wildcard());
  }

  void visit(const typing::ConstructedType&) override { out_.push_back(pat_); }

 private:
  managed_ptr<pattern_t> pat_;
  std::vector<managed_ptr<pattern_t>>& out_;
};

}  // namespace

void expand(managed_ptr<pattern_t> pat,
            std::vector<managed_ptr<pattern_t>>& out,
            const typing::Type& match_type) {
  PatternExpander v{pat, out};
  match_type.accept(v);
}

namespace {

collections::ArrayPtr<pattern_t> apply_substitutions_to_subpatterns(
    typing::Substitutions substitutions, bool enforce_timing_constraints,
    collections::ArrayPtr<pattern_t> subpatterns) {
  return make_managed<collections::ManagedArray<pattern_t>>(
      subpatterns->size(), [&](std::size_t i) {
        return (*subpatterns)[i]->apply_substitutions(
            substitutions, enforce_timing_constraints);
      });
}

}  // namespace

managed_ptr<pattern_t> pattern_t::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  auto pat = std::visit(
      overloaded{
          [&](const tuple_t& t) {
            return pattern_t::tuple(apply_substitutions_to_subpatterns(
                substitutions, enforce_timing_constraints, t.subpatterns));
          },
          [&](const record_t& r) {
            return pattern_t::record(apply_substitutions_to_subpatterns(
                substitutions, enforce_timing_constraints, r.subpatterns));
          },
          [](const wildcard_t&) { return pattern_t::wildcard(); },
          [&](const constructed_t& c) {
            return pattern_t::constructed(
                c.constructor, c.type_name,
                c.arg_type ? typing::apply_substitutions(
                                 c.arg_type, substitutions,
                                 typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                 enforce_timing_constraints)
                           : nullptr,
                apply_substitutions_to_subpatterns(
                    substitutions, enforce_timing_constraints, c.subpatterns));
          }},
      repr_);
  pat->field_ = field_;
  return pat;
}

void pattern_t::visit_subobjects(const ManagedVisitor& visitor) {
  if (field_) field_.accept(visitor);
  visit(overloaded{[&](auto& r) { r.subpatterns.accept(visitor); },
                   [&](wildcard_t&) {},
                   [&](constructed_t& c) {
                     c.constructor.accept(visitor);
                     c.type_name.accept(visitor);
                     c.arg_type.accept(visitor);
                     c.subpatterns.accept(visitor);
                   }},
        repr_);
}

TPattern::TPattern(const Location& location, typing::TypePtr type,
                   managed_ptr<pattern_t> pat,
                   managed_ptr<typing::ValEnv> bindings,
                   managed_ptr<bind_rule_t> bind_rule)
    : location(location),
      type(type),
      pat(pat),
      bindings(bindings),
      bind_rule(bind_rule) {}

managed_ptr<TPattern> TPattern::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TPattern>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      pat->apply_substitutions(substitutions, enforce_timing_constraints),
      bindings->apply_substitutions(substitutions, enforce_timing_constraints),
      bind_rule);
}

void TPattern::visit_subobjects(const ManagedVisitor& visitor) {
  type.accept(visitor);
  pat.accept(visitor);
  bindings.accept(visitor);
  bind_rule.accept(visitor);
}

const std::u8string dt_switch_t::DEFAULT_KEY = u8"_";

dt_switch_t::dt_switch_t(std::size_t index)
    : index(index),
      cases(collections::managed_map<ManagedString, dt_switch_subtree_t>({})) {}

dt_switch_t::~dt_switch_t() = default;
dt_switch_t::dt_switch_t(const dt_switch_t&) noexcept = default;
dt_switch_t& dt_switch_t::operator=(const dt_switch_t&) noexcept = default;

TExpr::TExpr(const Location& location, typing::TypePtr type,
             bool is_nonexpansive)
    : location(location), type(type), is_nonexpansive(is_nonexpansive) {}

TExpr::~TExpr() = default;
TExpr::Visitor::~Visitor() = default;

void TExpr::visit_subobjects(const ManagedVisitor& visitor) {
  type.accept(visitor);
  visit_texpr_subobjects(visitor);
}

void visit_subobjects(decision_tree_t& t, const ManagedVisitor& visitor) {
  visit(overloaded{[](auto&) {},
                   [&](dt_switch_t& d) { d.cases.accept(visitor); }},
        t);
}

managed_ptr<match_t> match_t::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  auto result = make_managed<match_t>();
  result->location = location;
  result->match_type = match_type;
  result->result_type = typing::apply_substitutions(
      result_type, substitutions, typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
      enforce_timing_constraints);
  result->outcomes = make_managed<collections::ManagedArray<outcome_t>>(
      outcomes->size(), [&](std::size_t i) {
        const auto& o = *(*outcomes)[i];
        return make_managed<outcome_t>(
            o.bindings->apply_substitutions(substitutions,
                                            enforce_timing_constraints),
            o.bind_rule,
            o.result->apply_substitutions(substitutions,
                                          enforce_timing_constraints));
      });
  result->decision_tree = decision_tree;
  result->nonexhaustive = nonexhaustive;
  return result;
}

void match_t::visit_subobjects(const ManagedVisitor& visitor) {
  match_type.accept(visitor);
  result_type.accept(visitor);
  outcomes.accept(visitor);
  emil::visit_subobjects(decision_tree, visitor);
}

namespace {

template <typename T>
bool all_nonexp(const T& types) {
  return std::all_of(types->begin(), types->end(),
                     [](const auto& t) { return t->is_nonexpansive; });
}

template <typename T>
collections::ArrayPtr<T> apply_substitutions_to_list(
    collections::ArrayPtr<T> exprs, typing::Substitutions substitutions,
    bool enforce_timing_constraints) {
  return make_managed<collections::ManagedArray<T>>(
      exprs->size(), [&](std::size_t i) {
        return (*exprs)[i]->apply_substitutions(substitutions,
                                                enforce_timing_constraints);
      });
}

}  // namespace

TBigintLiteralExpr::TBigintLiteralExpr(const Location& location,
                                       typing::TypePtr type,
                                       managed_ptr<bigint> value)
    : TExpr(location, type, true), value(value) {}

managed_ptr<TExpr> TBigintLiteralExpr::apply_substitutions(
    typing::Substitutions, bool) const {
  return make_managed<TBigintLiteralExpr>(location, type, value);
}

void TBigintLiteralExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  value.accept(visitor);
}

TIntLiteralExpr::TIntLiteralExpr(const Location& location, typing::TypePtr type,
                                 std::int64_t value)
    : TExpr(location, type, true), value(value) {}

managed_ptr<TExpr> TIntLiteralExpr::apply_substitutions(typing::Substitutions,
                                                        bool) const {
  return make_managed<TIntLiteralExpr>(location, type, value);
}

TFpLiteralExpr::TFpLiteralExpr(const Location& location, typing::TypePtr type,
                               double value)
    : TExpr(location, type, true), value(value) {}

managed_ptr<TExpr> TFpLiteralExpr::apply_substitutions(typing::Substitutions,
                                                       bool) const {
  return make_managed<TFpLiteralExpr>(location, type, value);
}

TStringLiteralExpr::TStringLiteralExpr(const Location& location,
                                       typing::TypePtr type, StringPtr value)
    : TExpr(location, type, true), value(value) {}

managed_ptr<TExpr> TStringLiteralExpr::apply_substitutions(
    typing::Substitutions, bool) const {
  return make_managed<TStringLiteralExpr>(location, type, value);
}

void TStringLiteralExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  value.accept(visitor);
}

TCharLiteralExpr::TCharLiteralExpr(const Location& location,
                                   typing::TypePtr type, char32_t value)
    : TExpr(location, type, true), value(value) {}

managed_ptr<TExpr> TCharLiteralExpr::apply_substitutions(typing::Substitutions,
                                                         bool) const {
  return make_managed<TCharLiteralExpr>(location, type, value);
}

TFstringLiteralExpr::TFstringLiteralExpr(
    const Location& location, typing::TypePtr type,
    collections::ArrayPtr<ManagedString> segments,
    collections::ArrayPtr<TExpr> substitutions)
    : TExpr(location, type, all_nonexp(substitutions)),
      segments(segments),
      substitutions(substitutions) {}

managed_ptr<TExpr> TFstringLiteralExpr::apply_substitutions(
    typing::Substitutions var_substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TFstringLiteralExpr>(
      location, type, segments,
      apply_substitutions_to_list(substitutions, var_substitutions,
                                  enforce_timing_constraints));
}

void TFstringLiteralExpr::visit_texpr_subobjects(
    const ManagedVisitor& visitor) {
  segments.accept(visitor);
  substitutions.accept(visitor);
}

TIdentifierExpr::TIdentifierExpr(
    const Location& location, typing::TypePtr type, typing::IdStatus status,
    collections::ArrayPtr<ManagedString> qualifiers,
    StringPtr canonical_identifier)
    : TExpr(location, type, true),
      status(status),
      qualifiers(qualifiers),
      canonical_identifier(canonical_identifier) {}

managed_ptr<TExpr> TIdentifierExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TIdentifierExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      status, qualifiers, canonical_identifier);
}

void TIdentifierExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  qualifiers.accept(visitor);
  canonical_identifier.accept(visitor);
}

TRecRowExpr::TRecRowExpr(const Location& location, typing::TypePtr type,
                         StringPtr label, managed_ptr<TExpr> value)
    : TExpr(location, type, value->is_nonexpansive),
      label(label),
      value(value) {}

managed_ptr<TRecRowExpr> TRecRowExpr::apply_substitutions_as_rec_row(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TRecRowExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      label,
      value->apply_substitutions(substitutions, enforce_timing_constraints));
}

void TRecRowExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  label.accept(visitor);
  value.accept(visitor);
}

TRecordExpr::TRecordExpr(const Location& location, typing::TypePtr type,
                         collections::ArrayPtr<TRecRowExpr> rows)
    : TExpr(location, type, all_nonexp(rows)), rows(rows) {}

managed_ptr<TExpr> TRecordExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TRecordExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      make_managed<collections::ManagedArray<TRecRowExpr>>(
          rows->size(), [&](std::size_t i) {
            return (*rows)[i]->apply_substitutions_as_rec_row(
                substitutions, enforce_timing_constraints);
          }));
}

void TRecordExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  rows.accept(visitor);
}

TTupleExpr::TTupleExpr(const Location& location, typing::TypePtr type,
                       collections::ArrayPtr<TExpr> exprs)
    : TExpr(location, type, all_nonexp(exprs)), exprs(exprs) {}

managed_ptr<TExpr> TTupleExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TTupleExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      apply_substitutions_to_list(exprs, substitutions,
                                  enforce_timing_constraints));
}

void TTupleExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  exprs.accept(visitor);
}

TSequencedExpr::TSequencedExpr(const Location& location, typing::TypePtr type,
                               collections::ArrayPtr<TExpr> exprs)
    : TExpr(location, type, false), exprs(exprs) {}

managed_ptr<TExpr> TSequencedExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TSequencedExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      apply_substitutions_to_list(exprs, substitutions,
                                  enforce_timing_constraints));
}

void TSequencedExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  exprs.accept(visitor);
}

TListExpr::TListExpr(const Location& location, typing::TypePtr type,
                     collections::ArrayPtr<TExpr> exprs)
    : TExpr(location, type, all_nonexp(exprs)), exprs(exprs) {}

managed_ptr<TExpr> TListExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TListExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      apply_substitutions_to_list(exprs, substitutions,
                                  enforce_timing_constraints));
}

void TListExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  exprs.accept(visitor);
}

TLetExpr::TLetExpr(const Location& location, typing::TypePtr type,
                   collections::ArrayPtr<TDecl> decls,
                   collections::ArrayPtr<TExpr> exprs)
    : TExpr(location, type, false), decls(decls), exprs(exprs) {}

managed_ptr<TExpr> TLetExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TLetExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      apply_substitutions_to_list(decls, substitutions,
                                  enforce_timing_constraints),
      apply_substitutions_to_list(exprs, substitutions,
                                  enforce_timing_constraints));
}

void TLetExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  decls.accept(visitor);
  exprs.accept(visitor);
}

TApplicationExpr::TApplicationExpr(const Location& location,
                                   typing::TypePtr type, bool is_nonexpansive,
                                   collections::ArrayPtr<TExpr> exprs)
    : TExpr(location, type, is_nonexpansive), exprs(exprs) {}

managed_ptr<TExpr> TApplicationExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TApplicationExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      is_nonexpansive,
      apply_substitutions_to_list(exprs, substitutions,
                                  enforce_timing_constraints));
}

void TApplicationExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  exprs.accept(visitor);
}

TCaseExpr::TCaseExpr(const Location& location, managed_ptr<TExpr> expr,
                     managed_ptr<match_t> match)
    : TExpr(location, match->result_type, false), expr(expr), match(match) {}

managed_ptr<TExpr> TCaseExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TCaseExpr>(
      location,
      expr->apply_substitutions(substitutions, enforce_timing_constraints),
      match->apply_substitutions(substitutions, enforce_timing_constraints));
}

void TCaseExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  expr.accept(visitor);
  match.accept(visitor);
}

TFnExpr::TFnExpr(const Location& location, typing::TypePtr type,
                 managed_ptr<match_t> match)
    : TExpr(location, type, true), match(match) {}

managed_ptr<TExpr> TFnExpr::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  return make_managed<TFnExpr>(
      location,
      typing::apply_substitutions(type, substitutions,
                                  typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                  enforce_timing_constraints),
      match->apply_substitutions(substitutions, enforce_timing_constraints));
}

void TFnExpr::visit_texpr_subobjects(const ManagedVisitor& visitor) {
  match.accept(visitor);
}

TDecl::~TDecl() = default;
TDecl::Visitor::~Visitor() = default;

TDecl::TDecl(const Location& location, managed_ptr<typing::Env> env)
    : location(location), env(env) {}

void TDecl::visit_subobjects(const ManagedVisitor& visitor) {
  env.accept(visitor);
  visit_tdecl_subobjects(visitor);
}

TValBind::TValBind(managed_ptr<match_t> match) : TValBind(match, nullptr) {}
TValBind::TValBind(managed_ptr<match_t> match, managed_ptr<TExpr> expr)
    : match(match), expr(expr) {}

void TValBind::visit_subobjects(const ManagedVisitor& visitor) {
  match.accept(visitor);
  if (expr) expr.accept(visitor);
}

TValDecl::TValDecl(const Location& location,
                   collections::ArrayPtr<TValBind> bindings,
                   managed_ptr<typing::Env> env)
    : TDecl(location, env), bindings(bindings) {}

managed_ptr<TDecl> TValDecl::apply_substitutions(
    typing::Substitutions substitutions,
    bool enforce_timing_constraints) const {
  auto new_bindings =
      make_managed<collections::ManagedArray<TValBind>>(bindings->size());
  std::transform(bindings->begin(), bindings->end(), new_bindings->begin(),
                 [&](const auto& p) {
                   return make_managed<TValBind>(
                       p->match->apply_substitutions(
                           substitutions, enforce_timing_constraints),
                       p->expr->apply_substitutions(
                           substitutions, enforce_timing_constraints));
                 });
  return make_managed<TValDecl>(
      location, new_bindings,
      env->apply_substitutions(substitutions, enforce_timing_constraints));
}

void TValDecl::visit_tdecl_subobjects(const ManagedVisitor& visitor) {
  bindings.accept(visitor);
}

TDtypeDecl::TDtypeDecl(const Location& location, managed_ptr<typing::Env> env)
    : TDecl(location, env) {}

TTopDecl::TTopDecl(const Location& location) : location(location) {}

TTopDecl::~TTopDecl() = default;
TTopDecl::Visitor::~Visitor() = default;

TDeclTopDecl::TDeclTopDecl(const Location& location, managed_ptr<TDecl> decl)
    : TTopDecl(location), decl(std::move(decl)) {}

void TDeclTopDecl::visit_subobjects(const ManagedVisitor& visitor) {
  decl.accept(visitor);
}

}  // namespace emil
