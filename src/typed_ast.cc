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
#include <iterator>
#include <stdexcept>
#include <variant>

#include "emil/collections.h"
#include "emil/tree.h"
#include "emil/types.h"

namespace emil {

pattern_t::pattern_t(repr r) : repr_(std::move(r)) {}

pattern_t pattern_t::wildcard() { return {wildcard_t{}}; }

pattern_t pattern_t::constructed(std::u8string constructor,
                                 managed_ptr<typing::TypeName> type_name,
                                 typing::TypePtr arg_type,
                                 std::vector<pattern_t> subpatterns) {
  return {constructed_t{std::move(constructor), type_name, arg_type,
                        std::move(subpatterns)}};
}

pattern_t pattern_t::tuple(std::vector<pattern_t> subpatterns) {
  return {tuple_t{std::move(subpatterns)}};
}

pattern_t pattern_t::record(std::vector<pattern_t> subpatterns) {
  assert(std::is_sorted(
      subpatterns.begin(), subpatterns.end(),
      [](const auto& l, const auto& r) { return l.field() < r.field(); }));
  return {record_t{std::move(subpatterns)}};
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

bool pattern_t::is_record_field() const { return !field_.empty(); }

bool pattern_t::is_constructed() const {
  return std::holds_alternative<constructed_t>(repr_);
}

const std::u8string& pattern_t::constructor() const {
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

const std::vector<pattern_t>& pattern_t::subpatterns() const {
  assert(!is_wildcard());
  return std::visit(
      overloaded{[](wildcard_t) -> const std::vector<pattern_t>& {
                   throw std::invalid_argument(
                       "May not call subpatterns() on wildcard pattern.");
                 },
                 [](const auto& r) -> const std::vector<pattern_t>& {
                   return r.subpatterns;
                 }},
      repr_);
}

const std::u8string& pattern_t::field() const {
  assert(is_record_field());
  return field_;
}

void pattern_t::set_field(std::u8string field) { field_ = std::move(field); }

namespace {

const pattern_t WILDCARD_PATTERN = pattern_t::wildcard();

class PatternExpander : public typing::TypeVisitor {
 public:
  PatternExpander(const pattern_t* pat, std::vector<const pattern_t*>& out)
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
      assert(subpatterns.size() == t.types()->size());
      for (std::size_t i = 0; i < subpatterns.size(); ++i) {
        pat_ = &subpatterns[i];
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
      auto it = pat_->subpatterns().begin();
      const auto end = pat_->subpatterns().end();
      for (const auto& row : *t.rows()) {
        if (it == end || *row.first < it->field()) {
          pat_ = &WILDCARD_PATTERN;
        } else {
          assert(*row.first == it->field());
          pat_ = &*it++;
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
  const pattern_t* pat_;
  std::vector<const pattern_t*>& out_;
};

}  // namespace

void pattern_t::expand(std::vector<const pattern_t*>& out,
                       const typing::Type& match_type) const {
  PatternExpander v{this, out};
  match_type.accept(v);
}

void pattern_t::apply_substitutions(typing::Substitutions substitutions) {
  std::visit(overloaded{[substitutions](auto& r) {
                          for (auto& p : r.subpatterns)
                            p.apply_substitutions(substitutions);
                        },
                        [](wildcard_t&) {},
                        [substitutions](constructed_t& c) {
                          c.arg_type = c.arg_type
                                           ? typing::apply_substitutions(
                                                 c.arg_type, substitutions)
                                           : nullptr;
                          for (auto& p : c.subpatterns)
                            p.apply_substitutions(substitutions);
                        }},
             repr_);
}

TPattern::TPattern(const Location& location, typing::TypePtr type,
                   pattern_t pat, managed_ptr<typing::ValEnv> bindings,
                   bind_rule_t bind_rule)
    : location(location),
      type(type),
      pat(std::move(pat)),
      bindings(bindings),
      bind_rule(std::move(bind_rule)) {}

std::unique_ptr<TPattern> TPattern::apply_substitutions(
    typing::Substitutions substitutions) const {
  auto new_pat = pat;
  new_pat.apply_substitutions(substitutions);
  return std::make_unique<TPattern>(
      location, typing::apply_substitutions(type, substitutions), new_pat,
      bindings->apply_substitutions(substitutions), bind_rule);
}

const std::u8string dt_switch_t::DEFAULT_KEY = u8"_";

TExpr::TExpr(const Location& location, typing::TypePtr type,
             bool is_nonexpansive)
    : location(location), type(type), is_nonexpansive(is_nonexpansive) {}

TExpr::~TExpr() = default;
TExpr::Visitor::~Visitor() = default;

match_t match_t::apply_substitutions(
    typing::Substitutions substitutions) const {
  match_t result{
      .location = location,
      .match_type = match_type,
      .result_type = typing::apply_substitutions(result_type, substitutions),
      .outcomes{},
      .decision_tree = decision_tree,
      .nonexhaustive = nonexhaustive};
  result.outcomes.reserve(outcomes.size());
  std::transform(outcomes.begin(), outcomes.end(),
                 back_inserter(result.outcomes), [&](const outcome_t& o) {
                   return outcome_t{
                       o.bindings->apply_substitutions(substitutions),
                       o.bind_rule,
                       o.result->apply_substitutions(substitutions)};
                 });
  return result;
}

namespace {

template <typename T>
bool all_nonexp(const T& types) {
  return std::all_of(types.begin(), types.end(),
                     [](const auto& t) { return t->is_nonexpansive; });
}

template <typename T>
std::vector<std::unique_ptr<T>> apply_substitutions_to_list(
    const std::vector<std::unique_ptr<T>>& exprs,
    typing::Substitutions substitutions) {
  std::vector<std::unique_ptr<T>> new_exprs;
  new_exprs.reserve(exprs.size());
  std::transform(
      exprs.begin(), exprs.end(), back_inserter(new_exprs),
      [&](const auto& e) { return e->apply_substitutions(substitutions); });
  return new_exprs;
}

template <typename T, typename U>
std::vector<std::pair<std::unique_ptr<T>, std::unique_ptr<U>>>
apply_substitutions_to_pairs(
    const std::vector<std::pair<std::unique_ptr<T>, std::unique_ptr<U>>>& pairs,
    typing::Substitutions substitutions) {
  std::vector<std::pair<std::unique_ptr<T>, std::unique_ptr<U>>> new_pairs;
  new_pairs.reserve(pairs.size());
  std::transform(
      pairs.begin(), pairs.end(), back_inserter(new_pairs), [&](const auto& p) {
        return std::make_pair(p.first->apply_substitutions(substitutions),
                              p.second->apply_substitutions(substitutions));
      });
  return new_pairs;
}

}  // namespace

TBigintLiteralExpr::TBigintLiteralExpr(const Location& location,
                                       typing::TypePtr type,
                                       managed_ptr<bigint> value)
    : TExpr(location, type, true), value(value) {}

std::unique_ptr<TExpr> TBigintLiteralExpr::apply_substitutions(
    typing::Substitutions) const {
  return std::make_unique<TBigintLiteralExpr>(location, type, value);
}

TIntLiteralExpr::TIntLiteralExpr(const Location& location, typing::TypePtr type,
                                 std::int64_t value)
    : TExpr(location, type, true), value(value) {}

std::unique_ptr<TExpr> TIntLiteralExpr::apply_substitutions(
    typing::Substitutions) const {
  return std::make_unique<TIntLiteralExpr>(location, type, value);
}

TFpLiteralExpr::TFpLiteralExpr(const Location& location, typing::TypePtr type,
                               double value)
    : TExpr(location, type, true), value(value) {}

std::unique_ptr<TExpr> TFpLiteralExpr::apply_substitutions(
    typing::Substitutions) const {
  return std::make_unique<TFpLiteralExpr>(location, type, value);
}

TStringLiteralExpr::TStringLiteralExpr(const Location& location,
                                       typing::TypePtr type, StringPtr value)
    : TExpr(location, type, true), value(value) {}

std::unique_ptr<TExpr> TStringLiteralExpr::apply_substitutions(
    typing::Substitutions) const {
  return std::make_unique<TStringLiteralExpr>(location, type, value);
}

TCharLiteralExpr::TCharLiteralExpr(const Location& location,
                                   typing::TypePtr type, char32_t value)
    : TExpr(location, type, true), value(value) {}

std::unique_ptr<TExpr> TCharLiteralExpr::apply_substitutions(
    typing::Substitutions) const {
  return std::make_unique<TCharLiteralExpr>(location, type, value);
}

TFstringLiteralExpr::TFstringLiteralExpr(
    const Location& location, typing::TypePtr type,
    collections::ConsPtr<ManagedString> segments,
    std::vector<std::unique_ptr<TExpr>> substitutions)
    : TExpr(location, type, all_nonexp(substitutions)),
      segments(segments),
      substitutions(std::move(substitutions)) {}

std::unique_ptr<TExpr> TFstringLiteralExpr::apply_substitutions(
    typing::Substitutions var_substitutions) const {
  return std::make_unique<TFstringLiteralExpr>(
      location, type, segments,
      apply_substitutions_to_list(substitutions, var_substitutions));
}

TIdentifierExpr::TIdentifierExpr(const Location& location, typing::TypePtr type,
                                 typing::IdStatus status,
                                 collections::ConsPtr<ManagedString> qualifiers,
                                 StringPtr canonical_identifier)
    : TExpr(location, type, true),
      status(status),
      qualifiers(qualifiers),
      canonical_identifier(canonical_identifier) {}

std::unique_ptr<TExpr> TIdentifierExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TIdentifierExpr>(
      location, typing::apply_substitutions(type, substitutions), status,
      qualifiers, canonical_identifier);
}

TRecRowExpr::TRecRowExpr(const Location& location, typing::TypePtr type,
                         StringPtr label, std::unique_ptr<TExpr> value)
    : TExpr(location, type, value->is_nonexpansive),
      label(label),
      value(std::move(value)) {}

std::unique_ptr<TRecRowExpr> TRecRowExpr::apply_substitutions_as_rec_row(
    typing::Substitutions substitutions) const {
  return std::make_unique<TRecRowExpr>(
      location, typing::apply_substitutions(type, substitutions), label,
      value->apply_substitutions(substitutions));
}

TRecordExpr::TRecordExpr(const Location& location, typing::TypePtr type,
                         std::vector<std::unique_ptr<TRecRowExpr>> rows)
    : TExpr(location, type, all_nonexp(rows)), rows(std::move(rows)) {}

std::unique_ptr<TExpr> TRecordExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  std::vector<std::unique_ptr<TRecRowExpr>> new_rows;
  new_rows.reserve(rows.size());
  std::transform(rows.begin(), rows.end(), back_inserter(new_rows),
                 [&](const auto& r) {
                   return r->apply_substitutions_as_rec_row(substitutions);
                 });
  return std::make_unique<TRecordExpr>(
      location, typing::apply_substitutions(type, substitutions),
      std::move(new_rows));
}

TTupleExpr::TTupleExpr(const Location& location, typing::TypePtr type,
                       std::vector<std::unique_ptr<TExpr>> exprs)
    : TExpr(location, type, all_nonexp(exprs)), exprs(std::move(exprs)) {}

std::unique_ptr<TExpr> TTupleExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TTupleExpr>(
      location, typing::apply_substitutions(type, substitutions),
      apply_substitutions_to_list(exprs, substitutions));
}

TSequencedExpr::TSequencedExpr(const Location& location, typing::TypePtr type,
                               std::vector<std::unique_ptr<TExpr>> exprs)
    : TExpr(location, type, false), exprs(std::move(exprs)) {}

std::unique_ptr<TExpr> TSequencedExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TSequencedExpr>(
      location, typing::apply_substitutions(type, substitutions),
      apply_substitutions_to_list(exprs, substitutions));
}

TListExpr::TListExpr(const Location& location, typing::TypePtr type,
                     std::vector<std::unique_ptr<TExpr>> exprs)
    : TExpr(location, type, all_nonexp(exprs)), exprs(std::move(exprs)) {}

std::unique_ptr<TExpr> TListExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TListExpr>(
      location, typing::apply_substitutions(type, substitutions),
      apply_substitutions_to_list(exprs, substitutions));
}

TLetExpr::TLetExpr(const Location& location, typing::TypePtr type,
                   std::vector<std::unique_ptr<TDecl>> decls,
                   std::vector<std::unique_ptr<TExpr>> exprs)
    : TExpr(location, type, false),
      decls(std::move(decls)),
      exprs(std::move(exprs)) {}

std::unique_ptr<TExpr> TLetExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TLetExpr>(
      location, typing::apply_substitutions(type, substitutions),
      apply_substitutions_to_list(decls, substitutions),
      apply_substitutions_to_list(exprs, substitutions));
}

TApplicationExpr::TApplicationExpr(const Location& location,
                                   typing::TypePtr type, bool is_nonexpansive,
                                   std::vector<std::unique_ptr<TExpr>> exprs)
    : TExpr(location, type, is_nonexpansive), exprs(std::move(exprs)) {}

std::unique_ptr<TExpr> TApplicationExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TApplicationExpr>(
      location, typing::apply_substitutions(type, substitutions),
      is_nonexpansive, apply_substitutions_to_list(exprs, substitutions));
}

TCaseExpr::TCaseExpr(const Location& location, std::unique_ptr<TExpr> expr,
                     match_t match)
    : TExpr(location, match.result_type, false),
      expr(std::move(expr)),
      match(std::move(match)) {}

std::unique_ptr<TExpr> TCaseExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TCaseExpr>(location,
                                     expr->apply_substitutions(substitutions),
                                     match.apply_substitutions(substitutions));
}

TFnExpr::TFnExpr(const Location& location, typing::TypePtr type, match_t match)
    : TExpr(location, type, true), match(std::move(match)) {}

std::unique_ptr<TExpr> TFnExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TFnExpr>(
      location, typing::apply_substitutions(type, substitutions),
      match.apply_substitutions(substitutions));
}

TDecl::~TDecl() = default;
TDecl::Visitor::~Visitor() = default;

TDecl::TDecl(const Location& location, managed_ptr<typing::Env> env)
    : location(location), env(env) {}

TValDecl::TValDecl(
    const Location& location,
    std::vector<std::pair<match_t, std::unique_ptr<TExpr>>> bindings,
    managed_ptr<typing::Env> env)
    : TDecl(location, env), bindings(std::move(bindings)) {}

std::unique_ptr<TDecl> TValDecl::apply_substitutions(
    typing::Substitutions substitutions) const {
  std::vector<std::pair<match_t, std::unique_ptr<TExpr>>> new_bindings;
  new_bindings.reserve(bindings.size());
  std::transform(bindings.begin(), bindings.end(), back_inserter(new_bindings),
                 [&](const auto& p) {
                   return std::make_pair(
                       p.first.apply_substitutions(substitutions),
                       p.second->apply_substitutions(substitutions));
                 });
  return std::make_unique<TValDecl>(location, std::move(new_bindings),
                                    env->apply_substitutions(substitutions));
}

TTopDecl::TTopDecl(const Location& location) : location(location) {}

TTopDecl::~TTopDecl() = default;
TTopDecl::Visitor::~Visitor() = default;

TExprTopDecl::TExprTopDecl(const Location& location,
                           std::unique_ptr<TExpr> expr,
                           managed_ptr<typing::TypeScheme> sigma)
    : TTopDecl(location), expr(std::move(expr)), sigma(sigma) {}

TDeclTopDecl::TDeclTopDecl(const Location& location,
                           std::unique_ptr<TDecl> decl)
    : TTopDecl(location), decl(std::move(decl)) {}

}  // namespace emil
