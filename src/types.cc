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

#include <algorithm>
#include <cassert>
#include <initializer_list>
#include <iterator>
#include <string>
#include <unordered_map>
#include <utility>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/tree.h"

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
  { StringPtr{t.name_ptr()} };  // NOLINT(readability/braces)
};                              // NOLINT(readability/braces)

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

bool operator==(const Stamp& l, const Stamp& r) { return l.id() == r.id(); }
bool operator==(std::uint64_t l, const Stamp& r) { return l == r.id(); }
bool operator==(const Stamp& l, std::uint64_t r) { return l.id() == r; }

bool operator!=(const Stamp& l, const Stamp& r) { return l.id() != r.id(); }
bool operator!=(std::uint64_t l, const Stamp& r) { return l != r.id(); }
bool operator!=(const Stamp& l, std::uint64_t r) { return l.id() != r; }

bool operator<(const Stamp& l, const Stamp& r) { return l.id() < r.id(); }
bool operator<(std::uint64_t l, const Stamp& r) { return l < r.id(); }
bool operator<(const Stamp& l, std::uint64_t r) { return l.id() < r; }

StampGenerator::StampGenerator() = default;

managed_ptr<Stamp> StampGenerator::operator()() {
  return make_managed<Stamp>(Stamp::token{}, next_id_++);
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

TypeVisitor::~TypeVisitor() = default;

Type::Type(StringSet free_variables, StampSet undetermined_types,
           StampSet type_names)
    : TypeObj(std::move(free_variables), std::move(type_names)),
      id_of_youngest_typename_(compute_max_id(this->type_names())),
      undetermined_types_(std::move(undetermined_types)) {}

void Type::visit_additional_subobjects(const ManagedVisitor& visitor) {
  undetermined_types_.accept(visitor);
  visit_additional_subobjects_of_type(visitor);
}

TypeWithAgeRestriction::TypeWithAgeRestriction(TypePtr type,
                                               std::uint64_t birthdate)
    : Type(type->free_variables(), type->undetermined_types(),
           type->type_names()),
      type_(std::move(type)),
      birthdate_(birthdate) {}

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

UndeterminedType::UndeterminedType(StampGenerator& stamper)
    : UndeterminedType(stamper()) {}

void UndeterminedType::visit_additional_subobjects_of_type(
    const ManagedVisitor& visitor) {
  name_.accept(visitor);
  stamp_.accept(visitor);
}

TypeName::TypeName(std::u8string_view name, managed_ptr<Stamp> stamp,
                   std::size_t arity)
    : TypeName(make_string(name), std::move(stamp), arity) {}

TypeName::TypeName(std::u8string_view name, StampGenerator& stamper,
                   std::size_t arity)
    : TypeName(name, stamper(), arity) {}

TypeName::TypeName(StringPtr name, managed_ptr<Stamp> stamp, std::size_t arity)
    : TypeObj(string_set(), stamp_set({stamp})),
      name_(std::move(name)),
      stamp_(std::move(stamp)),
      arity_(arity) {}

TypeName::TypeName(StringPtr name, StampGenerator& stamper, std::size_t arity)
    : TypeName(name, stamper(), arity) {}

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

RecordType::RecordType(StringMap<Type> rows, bool has_wildcard)
    : Type(merge_free_variables(rows), merge_undetermined_types(rows),
           merge_type_names(rows)),
      rows_(std::move(rows)),
      has_wildcard_(has_wildcard) {}

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

namespace {

class TypePrinter : public TypeVisitor {
 public:
  explicit TypePrinter(CanonicalizeUndeterminedTypes c)
      : h_(ctx().mgr->acquire_hold()), c_(c) {}

  std::u8string& contents() { return contents_; }

  void visit(const TypeWithAgeRestriction& t) override {
    t.type()->accept(*this);
  }

  void visit(const TypeVar& t) override { contents_ += t.name(); }

  void visit(const UndeterminedType& t) override {
    if (c_ == CanonicalizeUndeterminedTypes::NO) {
      contents_ += t.name();
      return;
    }
    const auto id = t.stamp()->id();
    const auto it = mappings_.find(id);
    std::uint64_t new_id;
    if (it == mappings_.end()) {
      new_id = mappings_.size();
      mappings_[id] = new_id;
    } else {
      new_id = it->second;
    }
    fmt::format_to(std::back_inserter(contents_), "'~{}", new_id);
  }

  void visit(const TupleType& t) override {
    contents_ += u8"(";
    bool first = true;
    for (const auto& type : *t.types()) {
      if (first)
        first = false;
      else
        contents_ += u8" * ";
      type->accept(*this);
    }
    contents_ += u8")";
  }

  void visit(const RecordType& t) override {
    contents_ += u8"{";
    bool first = true;
    for (const auto& entry : *t.rows()) {
      if (first)
        first = false;
      else
        contents_ += u8", ";
      contents_.append(entry.first->data(), entry.first->size());
      contents_ += u8": ";
      entry.second->accept(*this);
    }
    if (t.has_wildcard()) {
      if (!first) contents_ += u8", ";
      contents_ += u8"...";
    }
    contents_ += u8"}";
  }

  void visit(const FunctionType& t) override {
    t.param()->accept(*this);
    contents_ += u8" -> ";
    t.result()->accept(*this);
  }

  void visit(const ConstructedType& t) override {
    switch (t.types()->size()) {
      case 0:
        break;

      case 1:
        (*t.types()->begin())->accept(*this);
        contents_ += u8" ";
        break;

      default: {
        contents_ += u8"(";
        bool first = true;
        for (const auto& type : *t.types()) {
          if (first)
            first = false;
          else
            contents_ += u8", ";
          type->accept(*this);
        }
        contents_ += u8") ";
      }
    }
    contents_ += t.name_str();
  }

 private:
  MemoryManager::hold h_;
  const CanonicalizeUndeterminedTypes c_;
  std::unordered_map<std::uint64_t, std::uint64_t> mappings_;
  std::u8string contents_;
};

}  // namespace

std::u8string print_type(TypePtr t, CanonicalizeUndeterminedTypes c) {
  return print_type(*t, c);
}

std::u8string print_type(const Type& t, CanonicalizeUndeterminedTypes c) {
  TypePrinter printer{c};
  t.accept(printer);
  return std::move(printer.contents());
}

UnificationError::UnificationError(const std::string& msg)
    : hold_(ctx().mgr->acquire_hold()), full_msg_(msg) {}

UnificationError::UnificationError(const std::string& msg, TypePtr l, TypePtr r)
    : UnificationError(msg) {
  add_context(l, r);
}

void UnificationError::add_context(TypePtr l, TypePtr r) {
  fmt::format_to(back_inserter(full_msg_),
                 "\n----\nwhile trying to unify\n{}\nwith\n{}",
                 to_std_string(print_type(l)), to_std_string(print_type(r)));
  context_.emplace_back(std::move(l), std::move(r));
}

namespace {
class Substitutor : public TypeVisitor {
 public:
  TypePtr result;

  Substitutor(TypePtr orig, Substitutions substitutions,
              std::uint64_t maximum_type_name_id)
      : result(std::move(orig)),
        substitutions_(std::move(substitutions)),
        maximum_type_name_id_(maximum_type_name_id) {}

  void visit(const TypeWithAgeRestriction& t) override {
    result = make_managed<TypeWithAgeRestriction>(
        apply_substitutions(t.type(), substitutions_,
                            std::min(maximum_type_name_id_, t.birthdate())),
        t.birthdate());
  }

  void visit(const TypeVar&) override {}

  void visit(const UndeterminedType& t) override {
    const auto it = substitutions_->find(*t.stamp());
    if (it == substitutions_->cend()) return;
    const auto id = t.stamp()->id();
    const auto& r = it->second;
    if (r->id_of_youngest_typename() > std::min(maximum_type_name_id_, id)) {
      throw UnificationError(fmt::format(
          "Illegal substitution. {} (with constraint {}) can't be "
          "substituted by {} (with youngest type id {})",
          to_std_string(t.name()), maximum_type_name_id_,
          to_std_string(print_type(r)), r->id_of_youngest_typename()));
    }
    result = r->undetermined_types()->empty()
                 ? r
                 : make_managed<TypeWithAgeRestriction>(r, id);
  }

  void visit(const TupleType& t) override {
    result = make_managed<TupleType>(apply_substitutions_to_list(t.types()));
  }

  void visit(const RecordType& t) override {
    StringMap<Type> new_rows =
        collections::managed_map<ManagedString, Type>({});
    for (const auto& entry : *t.rows()) {
      new_rows = new_rows
                     ->insert(entry.first,
                              apply_substitutions(entry.second, substitutions_,
                                                  maximum_type_name_id_))
                     .first;
    }
    result = make_managed<RecordType>(std::move(new_rows), t.has_wildcard());
  }

  void visit(const FunctionType& t) override {
    result = make_managed<FunctionType>(
        apply_substitutions(t.param(), substitutions_, maximum_type_name_id_),
        apply_substitutions(t.result(), substitutions_, maximum_type_name_id_));
  }

  void visit(const ConstructedType& t) override {
    result = make_managed<ConstructedType>(
        t.name(), apply_substitutions_to_list(t.types()));
  }

 private:
  Substitutions substitutions_;
  std::uint64_t maximum_type_name_id_;

  TypeList apply_substitutions_to_list(const TypeList& l) const {
    return make_managed<collections::ManagedArray<Type>>(
        l->size(), [&l, this](std::size_t i) {
          return apply_substitutions(l->at(i), substitutions_,
                                     maximum_type_name_id_);
        });
  }
};

}  // namespace

TypePtr apply_substitutions(TypePtr t, Substitutions substitutions,
                            std::uint64_t maximum_type_name_id) {
  auto hold = ctx().mgr->acquire_hold();
  auto filtered_subs = substitutions->filter_keys(t->undetermined_types());
  if (filtered_subs->empty()) return t;
  Substitutor s{t, std::move(filtered_subs), maximum_type_name_id};
  t->accept(s);
  return std::move(s.result);
}

}  // namespace emil::typing
