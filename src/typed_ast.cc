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
#include <iterator>

#include "emil/types.h"

namespace emil {

TPattern::~TPattern() = default;
TPattern::Visitor::~Visitor() = default;

TExpr::~TExpr() = default;
TExpr::Visitor::~Visitor() = default;

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

TCaseExpr::TCaseExpr(
    const Location& location, typing::TypePtr type, std::unique_ptr<TExpr> expr,
    std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
        cases)
    : TExpr(location, type, false),
      expr(std::move(expr)),
      cases(std::move(cases)) {}

std::unique_ptr<TExpr> TCaseExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TCaseExpr>(
      location, typing::apply_substitutions(type, substitutions),
      expr->apply_substitutions(substitutions),
      apply_substitutions_to_pairs(cases, substitutions));
}

TFnExpr::TFnExpr(
    const Location& location, typing::TypePtr type,
    std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
        cases)
    : TExpr(location, type, true), cases(std::move(cases)) {}

std::unique_ptr<TExpr> TFnExpr::apply_substitutions(
    typing::Substitutions substitutions) const {
  return std::make_unique<TFnExpr>(
      location, typing::apply_substitutions(type, substitutions),
      apply_substitutions_to_pairs(cases, substitutions));
}

TDecl::~TDecl() = default;
TDecl::Visitor::~Visitor() = default;

TTopDecl::~TTopDecl() = default;
TTopDecl::Visitor::~Visitor() = default;

}  // namespace emil
