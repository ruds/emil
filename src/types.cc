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

#include <cassert>
#include <initializer_list>
#include <utility>

#include "emil/collections.h"
#include "emil/string.h"

namespace emil::typing {

namespace {

StringSet string_set(std::initializer_list<StringPtr> strings = {}) {
  return collections::managed_set<ManagedString>(strings);
}

template <typename T>
concept TypeObjWithNamePtr = requires(const T& t) {
  {StringPtr{t.name_ptr()}};  // NOLINT(readability/braces)
};                            // NOLINT(readability/braces)

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
StringSet merge_free_variables(const collections::ArrayPtr<Type>& types) {
  StringSet s = string_set();
  for (const auto& entry : *types) {
    s = std::move(s) | entry->free_variables();
  }
  return s;
}

}  // namespace

TypeObj::TypeObj(StringSet free_variables)
    : free_variables_(std::move(free_variables)) {}

TypeObj::~TypeObj() = default;

void TypeObj::visit_subobjects(const ManagedVisitor& visitor) {
  free_variables_.accept(visitor);
  visit_additional_subobjects(visitor);
}

TypeVar::TypeVar(std::u8string_view name) : TypeVar(make_string(name)) {}

TypeVar::TypeVar(StringPtr name)
    : Type(string_set({name})), name_(std::move(name)) {}

void TypeVar::visit_additional_subobjects(const ManagedVisitor& visitor) {
  name_.accept(visitor);
}

TypeName::TypeName(std::u8string_view name, std::size_t arity)
    : TypeName(make_string(name), arity) {}

TypeName::TypeName(StringPtr name, std::size_t arity)
    : Type(string_set()), name_(std::move(name)), arity_(arity) {}

void TypeName::visit_additional_subobjects(const ManagedVisitor& visitor) {
  name_.accept(visitor);
}

RecordType::RecordType(StringMap<Type> rows)
    : Type(merge_free_variables(rows)), rows_(std::move(rows)) {}

void RecordType::visit_additional_subobjects(const ManagedVisitor& visitor) {
  rows_.accept(visitor);
}

FunctionType::FunctionType(TypePtr param, TypePtr result)
    : Type(param->free_variables() | result->free_variables()),
      param_(std::move(param)),
      result_(std::move(result)) {}

void FunctionType::visit_additional_subobjects(const ManagedVisitor& visitor) {
  param_.accept(visitor);
  result_.accept(visitor);
}

ConstructedType::ConstructedType(managed_ptr<TypeName> name,
                                 collections::ArrayPtr<Type> types)
    : Type(merge_free_variables(types)),
      name_(std::move(name)),
      types_(std::move(types)) {
  assert(types->size() == name->arity());
}

void ConstructedType::visit_additional_subobjects(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
  types_.accept(visitor);
}

TypeFunction::TypeFunction(TypePtr t, collections::ArrayPtr<TypeVar> bound)
    : TypeObj(t->free_variables() - to_distinct_string_set(bound)),
      t_(std::move(t)),
      bound_(std::move(bound)) {}

void TypeFunction::visit_additional_subobjects(const ManagedVisitor& visitor) {
  t_.accept(visitor);
  bound_.accept(visitor);
}

TypeScheme::TypeScheme(TypePtr t, collections::ArrayPtr<TypeVar> bound)
    : TypeObj(t->free_variables() - to_distinct_string_set(bound)),
      t_(std::move(t)),
      bound_(std::move(bound)) {}

void TypeScheme::visit_additional_subobjects(const ManagedVisitor& visitor) {
  t_.accept(visitor);
  bound_.accept(visitor);
}

TypeStructure::TypeStructure(managed_ptr<TypeFunction> fn,
                             managed_ptr<ValEnv> env)
    : TypeObj(fn->free_variables() | env->free_variables()),
      fn_(std::move(fn)),
      env_(std::move(env)) {}

void TypeStructure::visit_additional_subobjects(const ManagedVisitor& visitor) {
  fn_.accept(visitor);
  env_.accept(visitor);
}

TypeEnv::TypeEnv(StringMap<TypeStructure> env)
    : TypeObj(merge_free_variables(env)), env_(std::move(env)) {}

std::optional<managed_ptr<TypeStructure>> TypeEnv::get(
    const std::u8string_view& key) const {
  return env_->get(key);
}

void TypeEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

ValueBinding::ValueBinding(managed_ptr<TypeScheme> scheme, IdStatus status)
    : TypeObj(scheme->free_variables()),
      scheme_(std::move(scheme)),
      status_(status) {}

void ValueBinding::visit_additional_subobjects(const ManagedVisitor& visitor) {
  scheme_.accept(visitor);
}

ValEnv::ValEnv(StringMap<ValueBinding> env)
    : TypeObj(merge_free_variables(env)), env_(std::move(env)) {}

std::optional<managed_ptr<ValueBinding>> ValEnv::get(
    const std::u8string_view& key) const {
  return env_->get(key);
}

void ValEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

Env::Env(managed_ptr<TypeEnv> type_env, managed_ptr<ValEnv> val_env)
    : TypeObj(type_env->free_variables() | val_env->free_variables()),
      type_env_(std::move(type_env)),
      val_env_(std::move(val_env)) {}

void Env::visit_additional_subobjects(const ManagedVisitor& visitor) {
  type_env_.accept(visitor);
  val_env_.accept(visitor);
}

Context::Context(collections::SetPtr<TypeName> type_names,
                 StringSet explicit_type_variables, managed_ptr<Env> env)
    : TypeObj(explicit_type_variables | env->free_variables()),
      names_(std::move(type_names)),
      vars_(std::move(explicit_type_variables)) {}

void Context::visit_additional_subobjects(const ManagedVisitor& visitor) {
  names_.accept(visitor);
  vars_.accept(visitor);
  env_.accept(visitor);
}

Basis::Basis(collections::SetPtr<TypeName> type_names, managed_ptr<Env> env)
    : TypeObj(env->free_variables()),
      names_(std::move(type_names)),
      env_(std::move(env)) {}

managed_ptr<Context> Basis::as_context() const {
  return make_managed<Context>(names_, string_set(), env_);
}

void Basis::visit_additional_subobjects(const ManagedVisitor& visitor) {
  names_.accept(visitor);
  env_.accept(visitor);
}

}  // namespace emil::typing
