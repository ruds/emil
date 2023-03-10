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

#include "emil/types.h"

#include <fmt/core.h>

#include <cassert>
#include <initializer_list>
#include <iterator>
#include <string>
#include <utility>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/strconvert.h"
#include "emil/string.h"

namespace emil::typing {

namespace {

StringSet string_set(std::initializer_list<StringPtr> strings = {}) {
  return collections::managed_set<ManagedString>(strings);
}

StampSet stamp_set(std::initializer_list<managed_ptr<Stamp>> stamps = {}) {
  return collections::managed_set<Stamp>(stamps);
}

template <typename T>
concept TypeObjWithNamePtr = requires(const T& t) {
                               {
                                 StringPtr{t.name_ptr()}
                               };  // NOLINT(readability/braces)
                             };    // NOLINT(readability/braces)

template <TypeObjWithNamePtr T>
StringSet to_distinct_string_set(const collections::ArrayPtr<T>& vars) {
  auto s = string_set();
  for (const auto& v : *vars) {
    auto r = s->insert(v->name_ptr());
    assert(r.second);
    s = std::move(r.first);
  }
  return s;
}

// requires hold
template <TypeObjType T>
StringSet merge_free_variables(const StringMap<T>& m) {
  StringSet s = string_set();
  for (const auto& entry : *m) {
    s = std::move(s) | entry.second->free_variables();
  }
  return s;
}

// requires hold
StringSet merge_free_variables(const TypeList& types) {
  StringSet s = string_set();
  for (const auto& entry : *types) {
    s = std::move(s) | entry->free_variables();
  }
  return s;
}

// requires hold
template <TypeObjType T>
StampSet merge_undetermined_types(const StringMap<T>& m) {
  StampSet s = stamp_set();
  for (const auto& entry : *m) {
    s = std::move(s) | entry.second->undetermined_types();
  }
  return s;
}

// requires hold
StampSet merge_undetermined_types(const TypeList& types) {
  StampSet s = stamp_set();
  for (const auto& entry : *types) {
    s = std::move(s) | entry->undetermined_types();
  }
  return s;
}

// requires hold
template <TypeObjType T>
StampSet merge_type_names(const StringMap<T>& m) {
  StampSet s = stamp_set();
  for (const auto& entry : *m) {
    s = std::move(s) | entry.second->type_names();
  }
  return s;
}

// requires hold
StampSet merge_type_names(const TypeList& types) {
  StampSet s = stamp_set();
  for (const auto& entry : *types) {
    s = std::move(s) | entry->type_names();
  }
  return s;
}

// Requires hold.
std::uint64_t compute_max_id(StampSet s) {
  if (s->empty()) return 0;
  return (*s->crbegin())->id();
}
}  // namespace

Stamp::Stamp(token, std::uint64_t id) : id_(id) {}

bool operator<(const Stamp& l, const Stamp& r) { return l.id() < r.id(); }
bool operator<(std::uint64_t l, const Stamp& r) { return l < r.id(); }
bool operator<(const Stamp& l, std::uint64_t r) { return l.id() < r; }

StampGenerator::StampGenerator() = default;

managed_ptr<Stamp> StampGenerator::operator()() {
  return make_managed<Stamp>(Stamp::token{}, ++next_id_);
}

TypeObj::TypeObj(StringSet free_variables, StampSet type_names)
    : free_variables_(std::move(free_variables)),
      type_names_(std::move(type_names)) {}

TypeObj::~TypeObj() = default;

void TypeObj::visit_subobjects(const ManagedVisitor& visitor) {
  free_variables_.accept(visitor);
  type_names_.accept(visitor);
  visit_additional_subobjects(visitor);
}

Type::Type(StringSet free_variables, StampSet undetermined_types,
           StampSet type_names)
    : TypeObj(std::move(free_variables), std::move(type_names)),
      id_of_youngest_typename_(compute_max_id(this->type_names())),
      undetermined_types_(std::move(undetermined_types)) {}

void Type::visit_additional_subobjects(const ManagedVisitor& visitor) {
  undetermined_types_.accept(visitor);
  visit_additional_subobjects_of_type(visitor);
}

TypeWithAgeRestriction::TypeWithAgeRestriction(TypePtr type, std::uint64_t age)
    : Type(type->free_variables(), type->undetermined_types(),
           type->type_names()),
      type_(std::move(type)),
      age_(age) {}

void TypeWithAgeRestriction::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  type_.accept(visitor);
}

TypeVar::TypeVar(std::u8string_view name) : TypeVar(make_string(name)) {}

TypeVar::TypeVar(StringPtr name)
    : Type(string_set({name}), stamp_set(), stamp_set()),
      name_(std::move(name)) {}

void TypeVar::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
}

UndeterminedType::UndeterminedType(managed_ptr<Stamp> stamp)
    : Type(string_set(), stamp_set({stamp}), stamp_set()),
      name_(make_string(to_u8string(fmt::format("'~{}", stamp->id())))),
      stamp_(std::move(stamp)) {}

void UndeterminedType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
  stamp_.accept(visitor);
}

TypeName::TypeName(std::u8string_view name, managed_ptr<Stamp> stamp,
                   std::size_t arity)
    : TypeName(make_string(name), std::move(stamp), arity) {}

TypeName::TypeName(StringPtr name, managed_ptr<Stamp> stamp, std::size_t arity)
    : TypeObj(string_set(), stamp_set({stamp})),
      name_(std::move(name)),
      stamp_(std::move(stamp)),
      arity_(arity) {}

void TypeName::visit_additional_subobjects(const ManagedVisitor& visitor) {
  name_.accept(visitor);
  stamp_.accept(visitor);
}

TupleType::TupleType(TypeList types)
    : Type(merge_free_variables(types), merge_undetermined_types(types),
           merge_type_names(types)),
      types_(std::move(types)) {}

void TupleType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  types_.accept(visitor);
}

RecordType::RecordType(StringMap<Type> rows)
    : Type(merge_free_variables(rows), merge_undetermined_types(rows),
           merge_type_names(rows)),
      rows_(std::move(rows)) {}

void RecordType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  rows_.accept(visitor);
}

FunctionType::FunctionType(TypePtr param, TypePtr result)
    : Type(param->free_variables() | result->free_variables(),
           param->undetermined_types() | result->undetermined_types(),
           param->type_names() | result->type_names()),
      param_(std::move(param)),
      result_(std::move(result)) {}

void FunctionType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  param_.accept(visitor);
  result_.accept(visitor);
}

ConstructedType::ConstructedType(managed_ptr<TypeName> name, TypeList types)
    : Type(merge_free_variables(types), merge_undetermined_types(types),
           merge_type_names(types) | name->type_names()),
      name_(std::move(name)),
      types_(std::move(types)) {
  assert(types_->size() == name_->arity());
}

void ConstructedType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
  types_.accept(visitor);
}

TypeFunction::TypeFunction(TypePtr t, collections::ArrayPtr<TypeVar> bound)
    : TypeObj(t->free_variables() - to_distinct_string_set(bound),
              t->type_names()),
      t_(std::move(t)),
      bound_(std::move(bound)) {}

void TypeFunction::visit_additional_subobjects(const ManagedVisitor& visitor) {
  t_.accept(visitor);
  bound_.accept(visitor);
}

TypeScheme::TypeScheme(TypePtr t, collections::ArrayPtr<TypeVar> bound)
    : TypeObj(t->free_variables() - to_distinct_string_set(bound),
              t->type_names()),
      t_(std::move(t)),
      bound_(std::move(bound)) {}

void TypeScheme::visit_additional_subobjects(const ManagedVisitor& visitor) {
  t_.accept(visitor);
  bound_.accept(visitor);
}

TypeStructure::TypeStructure(managed_ptr<TypeFunction> fn,
                             managed_ptr<ValEnv> env)
    : TypeObj(fn->free_variables() | env->free_variables(),
              fn->type_names() | env->type_names()),
      fn_(std::move(fn)),
      env_(std::move(env)) {}

void TypeStructure::visit_additional_subobjects(const ManagedVisitor& visitor) {
  fn_.accept(visitor);
  env_.accept(visitor);
}

TypeEnv::TypeEnv(StringMap<TypeStructure> env)
    : TypeObj(merge_free_variables(env), merge_type_names(env)),
      env_(std::move(env)) {}

std::optional<managed_ptr<TypeStructure>> TypeEnv::get(
    const std::u8string_view& key) const {
  return env_->get(key);
}

void TypeEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

ValueBinding::ValueBinding(managed_ptr<TypeScheme> scheme, IdStatus status)
    : TypeObj(scheme->free_variables(), scheme->type_names()),
      scheme_(std::move(scheme)),
      status_(status) {}

void ValueBinding::visit_additional_subobjects(const ManagedVisitor& visitor) {
  scheme_.accept(visitor);
}

ValEnv::ValEnv(StringMap<ValueBinding> env)
    : TypeObj(merge_free_variables(env), merge_type_names(env)),
      env_(std::move(env)) {}

std::optional<managed_ptr<ValueBinding>> ValEnv::get(
    const std::u8string_view& key) const {
  return env_->get(key);
}

void ValEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

Env::Env(managed_ptr<TypeEnv> type_env, managed_ptr<ValEnv> val_env)
    : TypeObj(type_env->free_variables() | val_env->free_variables(),
              type_env->type_names() | val_env->type_names()),
      type_env_(std::move(type_env)),
      val_env_(std::move(val_env)) {}

void Env::visit_additional_subobjects(const ManagedVisitor& visitor) {
  type_env_.accept(visitor);
  val_env_.accept(visitor);
}

Context::Context(StampSet type_names, StringSet explicit_type_variables,
                 managed_ptr<Env> env)
    : TypeObj(explicit_type_variables | env->free_variables(),
              std::move(type_names)),
      vars_(std::move(explicit_type_variables)) {}

void Context::visit_additional_subobjects(const ManagedVisitor& visitor) {
  vars_.accept(visitor);
  env_.accept(visitor);
}

Basis::Basis(StampSet type_names, managed_ptr<Env> env)
    : TypeObj(env->free_variables(), std::move(type_names)),
      env_(std::move(env)) {}

managed_ptr<Context> Basis::as_context() const {
  return make_managed<Context>(type_names(), string_set(), env_);
}

void Basis::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

managed_ptr<TypeEnv> operator+(const managed_ptr<TypeEnv>& l,
                               const managed_ptr<TypeEnv>& r) {
  return make_managed<TypeEnv>(l->env() | r->env());
}
managed_ptr<ValEnv> operator+(const managed_ptr<ValEnv>& l,
                              const managed_ptr<ValEnv>& r) {
  return make_managed<ValEnv>(l->env() | r->env());
}

managed_ptr<Env> operator+(const managed_ptr<Env>& l,
                           const managed_ptr<Env>& r) {
  return make_managed<Env>(l->type_env() + r->type_env(),
                           l->val_env() + r->val_env());
}

managed_ptr<Basis> operator+(const managed_ptr<Basis>& B,
                             const managed_ptr<Env>& E) {
  return make_managed<Basis>(B->type_names() | E->type_names(), B->env() + E);
}

}  // namespace emil::typing
