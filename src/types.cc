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

StampSet stamp_set(std::initializer_list<managed_ptr<Stamp>> stamps = {}) {
  return collections::managed_set<Stamp>(stamps);
}

TypeList type_list(std::initializer_list<managed_ptr<Type>> types = {}) {
  return collections::make_array(types);
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

TypeVar::TypeVar(std::u8string_view name) : TypeVar(make_string(name)) {}

TypeVar::TypeVar(StringPtr name)
    : Type(string_set({name}), stamp_set()), name_(std::move(name)) {}

void TypeVar::visit_additional_subobjects(const ManagedVisitor& visitor) {
  name_.accept(visitor);
}

UndeterminedType::UndeterminedType(std::u8string_view name,
                                   managed_ptr<Stamp> stamp)
    : UndeterminedType(make_string(name), std::move(stamp)) {}

UndeterminedType::UndeterminedType(StringPtr name, managed_ptr<Stamp> stamp)
    : Type(string_set({name}), stamp_set()),
      name_(std::move(name)),
      stamp_(std::move(stamp)) {}

void UndeterminedType::visit_additional_subobjects(
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
    : Type(merge_free_variables(types), merge_type_names(types)),
      types_(std::move(types)) {}

void TupleType::visit_additional_subobjects(const ManagedVisitor& visitor) {
  types_.accept(visitor);
}

RecordType::RecordType(StringMap<Type> rows)
    : Type(merge_free_variables(rows), merge_type_names(rows)),
      rows_(std::move(rows)) {}

void RecordType::visit_additional_subobjects(const ManagedVisitor& visitor) {
  rows_.accept(visitor);
}

FunctionType::FunctionType(TypePtr param, TypePtr result)
    : Type(param->free_variables() | result->free_variables(),
           param->type_names() | result->type_names()),
      param_(std::move(param)),
      result_(std::move(result)) {}

void FunctionType::visit_additional_subobjects(const ManagedVisitor& visitor) {
  param_.accept(visitor);
  result_.accept(visitor);
}

ConstructedType::ConstructedType(managed_ptr<TypeName> name, TypeList types)
    : Type(merge_free_variables(types),
           merge_type_names(types) | name->type_names()),
      name_(std::move(name)),
      types_(std::move(types)) {
  assert(types_->size() == name_->arity());
}

void ConstructedType::visit_additional_subobjects(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
  types_.accept(visitor);
}

namespace {

TypePtr construct_type0(managed_ptr<Stamp>&& stamp, std::u8string_view name) {
  return make_managed<ConstructedType>(
      make_managed<TypeName>(name, std::move(stamp), 0), type_list());
}

}  // namespace

BuiltinTypes::BuiltinTypes(managed_ptr<Stamp> bi, managed_ptr<Stamp> i,
                           managed_ptr<Stamp> by, managed_ptr<Stamp> fl,
                           managed_ptr<Stamp> bo, managed_ptr<Stamp> c,
                           managed_ptr<Stamp> s, managed_ptr<Stamp> l)
    : TypeObj(string_set(), stamp_set({bi, i, by, fl, bo, c, s, l})),
      bi_(construct_type0(std::move(bi), u8"bigint")),
      i_(construct_type0(std::move(i), u8"int")),
      by_(construct_type0(std::move(by), u8"byte")),
      fl_(construct_type0(std::move(fl), u8"float")),
      bo_(construct_type0(std::move(bo), u8"bool")),
      c_(construct_type0(std::move(c), u8"char")),
      s_(construct_type0(std::move(s), u8"string")),
      l_(make_managed<TypeName>(u8"list", l, 1)) {}

TypePtr BuiltinTypes::tuple_type(TypeList types) const {
  return make_managed<TupleType>(std::move(types));
}

TypePtr BuiltinTypes::list_type(TypePtr type) const {
  return make_managed<ConstructedType>(l_, type_list({std::move(type)}));
}

TypePtr BuiltinTypes::record_type(StringMap<Type> rows) const {
  return make_managed<RecordType>(std::move(rows));
}

void BuiltinTypes::visit_additional_subobjects(const ManagedVisitor& visitor) {
  bi_.accept(visitor);
  i_.accept(visitor);
  by_.accept(visitor);
  fl_.accept(visitor);
  bo_.accept(visitor);
  c_.accept(visitor);
  s_.accept(visitor);
  l_.accept(visitor);
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
