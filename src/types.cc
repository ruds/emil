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
#include <optional>
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

TypeList type_list(std::initializer_list<managed_ptr<Type>> types = {}) {
  return collections::make_array(types);
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
      types_(std::move(types)) {
  assert(types_->size() != 1);
}

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

namespace {

class SchemeInstantiator : public TypeVisitor {
 public:
  TypePtr type;

  SchemeInstantiator(StampGenerator& stamper,
                     collections::ArrayPtr<TypeVar> bound)
      : stamper_(stamper), bound_(bound) {
    for (const auto& v : *bound_) {
      mapping_ =
          mapping_
              ->insert(v->name_ptr(), make_managed<UndeterminedType>(stamper_))
              .first;
    }
  }

  void visit(const TypeWithAgeRestriction& t) override {
    t.type()->accept(*this);
    type = make_managed<TypeWithAgeRestriction>(type, t.birthdate());
  }

  void visit(const TypeVar& t) override {
    const auto it = mapping_->find(t.name());
    type = it == mapping_->cend() ? make_managed<TypeVar>(t.name_ptr())
                                  : it->second;
  }

  void visit(const UndeterminedType& t) override {
    type = make_managed<UndeterminedType>(t.stamp());
  }

  void visit(const TupleType& t) override {
    auto types = make_managed<collections::ManagedArray<Type>>(
        t.types()->size(), [&](std::size_t i) {
          (*t.types())[i]->accept(*this);
          return type;
        });
    type = make_managed<TupleType>(std::move(types));
  }

  void visit(const RecordType& t) override {
    auto rows = collections::managed_map<ManagedString, Type>({});
    for (const auto& r : *t.rows()) {
      r.second->accept(*this);
      rows = rows->insert(r.first, type).first;
    }
    type = make_managed<RecordType>(std::move(rows), t.has_wildcard());
  }

  void visit(const FunctionType& t) override {
    t.param()->accept(*this);
    auto param = type;
    t.result()->accept(*this);
    type = make_managed<FunctionType>(param, type);
  }

  void visit(const ConstructedType& t) override {
    auto types = make_managed<collections::ManagedArray<Type>>(
        t.types()->size(), [&](std::size_t i) {
          (*t.types())[i]->accept(*this);
          return type;
        });
    type = make_managed<ConstructedType>(t.name(), std::move(types));
  }

 private:
  StampGenerator& stamper_;
  collections::ArrayPtr<TypeVar> bound_;
  StringMap<Type> mapping_ = collections::managed_map<ManagedString, Type>({});
};

}  // namespace

TypePtr TypeScheme::instantiate(StampGenerator& stamper) const {
  auto hold = ctx().mgr->acquire_hold();
  SchemeInstantiator s{stamper, bound_};
  t_->accept(s);
  return s.type;
}

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
    std::u8string_view key) const {
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

std::u8string canonicalize_val_id(std::u8string_view id, bool is_op,
                                  bool is_prefix_op) {
  assert(!is_prefix_op || is_op);
  if (!is_op) return std::u8string(id);
  std::u8string out = u8"(";
  if (is_prefix_op) out += u8"prefix ";
  out += id;
  out += u8")";
  return out;
}

ValEnv::ValEnv(StringMap<ValueBinding> env)
    : TypeObj(merge_free_variables(env), merge_type_names(env)),
      env_(std::move(env)) {}

std::optional<managed_ptr<ValueBinding>> ValEnv::get(
    std::u8string_view key) const {
  return env_->get(key);
}

void ValEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
}

Env::Env(managed_ptr<StrEnv> str_env, managed_ptr<TypeEnv> type_env,
         managed_ptr<ValEnv> val_env)
    : TypeObj(str_env->free_variables() | type_env->free_variables() |
                  val_env->free_variables(),
              str_env->type_names() | type_env->type_names() |
                  val_env->type_names()),
      str_env_(std::move(str_env)),
      type_env_(std::move(type_env)),
      val_env_(std::move(val_env)) {}

std::optional<managed_ptr<ValueBinding>> Env::lookup_val(
    const std::vector<std::u8string>& qualifiers, std::u8string_view id) const {
  const Env* e = this;
  for (const auto& q : qualifiers) {
    const auto r = e->str_env()->get(q);
    if (r) {
      e = &**r;
    } else {
      return std::nullopt;
    }
  }
  return e->val_env()->get(id);
}

managed_ptr<StrEnv> Env::str_env() const { return str_env_; }

void Env::visit_additional_subobjects(const ManagedVisitor& visitor) {
  str_env_.accept(visitor);
  type_env_.accept(visitor);
  val_env_.accept(visitor);
}

StrEnv::StrEnv(StringMap<Env> env)
    : TypeObj(merge_free_variables(env), merge_type_names(env)),
      env_(std::move(env)) {}

std::optional<managed_ptr<Env>> StrEnv::get(std::u8string_view key) const {
  return env_->get(key);
}

void StrEnv::visit_additional_subobjects(const ManagedVisitor& visitor) {
  env_.accept(visitor);
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

managed_ptr<StrEnv> operator+(const managed_ptr<StrEnv>& l,
                              const managed_ptr<StrEnv>& r) {
  return make_managed<StrEnv>(l->env() | r->env());
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
  return make_managed<Env>(l->str_env() + r->str_env(),
                           l->type_env() + r->type_env(),
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

/**
 * Compute the substitution for a variable in context.
 *
 * Given that `var` is mapped to `type` in the substitution mapping,
 * determine the actual type that should be substituted for `var`
 * based on the maximum type id constraint. Throws a UnificationError
 * if the substitution would be illegal (i.e. type contains a
 * too-young typename).
 */
TypePtr compute_single_substitution(const UndeterminedType& var, TypePtr type,
                                    std::uint64_t max_id) {
  const auto id = var.stamp()->id();
  if (type->id_of_youngest_typename() > std::min(max_id, id)) {
    throw UnificationError(fmt::format(
        "Illegal substitution. {} (with constraint {}) can't be "
        "substituted by {} (with youngest type id {})",
        to_std_string(var.name()), max_id, to_std_string(print_type(type)),
        type->id_of_youngest_typename()));
  }
  return type->undetermined_types()->empty()
             ? type
             : make_managed<TypeWithAgeRestriction>(type, id);
}

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
    result = compute_single_substitution(t, it->second, maximum_type_name_id_);
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

namespace {

/**
 * Add a new substitution mapping v to t.
 */
void add_substitution(Substitutions& all_subs, Substitutions& new_subs,
                      const UndeterminedType& v, TypePtr t) {
  const auto& stamp = v.stamp();
  if (t->undetermined_types()->contains(*stamp)) {
    throw UnificationError(
        fmt::format("Recursive substitution failure: cannot map {} to {}",
                    to_std_string(v.name()), to_std_string(print_type(t))));
  }
  all_subs = all_subs->insert(stamp, t).first;
  new_subs = new_subs->insert(stamp, t).first;
  for (const auto& entry : *all_subs) {
    if (entry.second->undetermined_types()->contains(*stamp)) {
      auto subbed = apply_substitutions(entry.second, all_subs);
      all_subs = all_subs->insert(entry.first, subbed).first;
      new_subs = new_subs->insert(entry.first, subbed).first;
    }
  }
}

/**
 * The base class for the second visitor (which visits r) in unify's double
 * dispatch.
 *
 * This class provides implementations of `visit` which will work except when
 * `l` is of the same type as `r`. Namely,
 *
 * - TypeWithAgeRestriction cracks open the wrapper and re-visits the
 *   wrapped type.
 *
 * - UndeterminedType either applies an exisiting substition and
 *   re-visits or creates a new substitution.
 *
 * - The remaining types throw a UnificationError indicating that `l`
 *   and `r` are of different types and cannot be unified.
 *
 * Subclasses should (usually) just override the `visit` overload that
 * corresponds to `l` and `r` having the same type.
 */
class UnifierBase : public TypeVisitor {
 public:
  unification_t result;

  void visit(const TypeWithAgeRestriction& r) final {
    orig_r_ = r.type();
    max_id_r_ = std::min(max_id_r_, r.birthdate());
    orig_r_->accept(*this);
    assert(result.unified_type->id_of_youngest_typename() < r.birthdate());
    if (!result.unified_type->undetermined_types()->empty()) {
      result.unified_type = make_managed<TypeWithAgeRestriction>(
          result.unified_type, r.birthdate());
    }
  }

  void visit(const TypeVar&) override {
    throw UnificationError(
        fmt::format("Cannot unify {} with type variable", type_name_), orig_l_,
        orig_r_);
  }

  void visit(const UndeterminedType& r) final {
    const auto it = substitutions_->find(*r.stamp());
    if (it == substitutions_->cend()) {
      try {
        result.unified_type =
            compute_single_substitution(r, orig_l_, max_id_r_);
      } catch (UnificationError& e) {
        e.add_context(orig_l_, orig_r_);
        throw;
      }
      add_substitution(substitutions_, result.new_substitutions, r, orig_l_);
      return;
    }
    try {
      orig_r_ = compute_single_substitution(r, it->second, max_id_r_);
    } catch (UnificationError& e) {
      e.add_context(orig_l_, orig_r_);
      throw;
    }
    orig_r_->accept(*this);
  }

  void visit(const TupleType&) override {
    throw UnificationError(
        fmt::format("Cannot unify {} with tuple type", type_name_), orig_l_,
        orig_r_);
  }

  void visit(const RecordType&) override {
    throw UnificationError(
        fmt::format("Cannot unify {} with record type", type_name_), orig_l_,
        orig_r_);
  }

  void visit(const FunctionType&) override {
    throw UnificationError(
        fmt::format("Cannot unify {} with function type", type_name_), orig_l_,
        orig_r_);
  }

  void visit(const ConstructedType&) override {
    throw UnificationError(
        fmt::format("Cannot unify {} with constructed type", type_name_),
        orig_l_, orig_r_);
  }

 protected:
  UnifierBase(std::string_view type_name, TypePtr orig_l, TypePtr orig_r,
              Substitutions& substitutions, std::uint64_t max_id_r)
      : type_name_(type_name),
        orig_l_(std::move(orig_l)),
        orig_r_(std::move(orig_r)),
        substitutions_(substitutions),
        max_id_r_(max_id_r) {}

  const TypePtr& orig_l() const { return orig_l_; }
  const TypePtr& orig_r() const { return orig_r_; }
  Substitutions& substitutions() { return substitutions_; }
  std::uint64_t max_id_r() const { return max_id_r_; }

 private:
  std::string_view type_name_;
  TypePtr orig_l_;
  TypePtr orig_r_;
  Substitutions& substitutions_;
  std::uint64_t max_id_r_;
};

/** Performs unification when l is a type variable. */
class TypeVarUnifier : public UnifierBase {
 public:
  TypeVarUnifier(const TypeVar& l, TypePtr orig_l, TypePtr orig_r,
                 Substitutions& substitutions, std::uint64_t max_id_r)
      : UnifierBase("type variable", std::move(orig_l), std::move(orig_r),
                    substitutions, max_id_r),
        l_(l) {}

  void visit(const TypeVar& r) override {
    if (l_.name() != r.name()) {
      throw UnificationError(
          fmt::format("A type variable can only unify with itself. {} != {}",
                      to_std_string(l_.name()), to_std_string(r.name())),
          orig_l(), orig_r());
    }
    result.unified_type = orig_l();
  }

 private:
  const TypeVar& l_;
};

/** Performs unification when l is an undetermined type. */
class UndeterminedUnifier : public TypeVisitor {
 public:
  unification_t result;

  UndeterminedUnifier(const UndeterminedType& l, TypePtr orig_l, TypePtr orig_r,
                      Substitutions& substitutions, std::uint64_t max_id_l,
                      std::uint64_t max_id_r)
      : l_(l),
        orig_l_(std::move(orig_l)),
        orig_r_(std::move(orig_r)),
        substitutions_(substitutions),
        max_id_l_(max_id_l),
        max_id_r_(max_id_r) {}

  void visit(const TypeWithAgeRestriction& r) override {
    orig_r_ = r.type();
    max_id_r_ = std::min(max_id_r_, r.birthdate());
    orig_r_->accept(*this);
    assert(result.unified_type->id_of_youngest_typename() < r.birthdate());
    if (!result.unified_type->undetermined_types()->empty()) {
      result.unified_type = make_managed<TypeWithAgeRestriction>(
          result.unified_type, r.birthdate());
    }
  }

  void visit(const TypeVar&) override { unify_by_substitution(); }

  void visit(const UndeterminedType& r) override {
    if (l_.name() == r.name()) {
      result.unified_type = orig_l_;
      return;
    }
    const auto it = substitutions_->find(*r.stamp());
    if (it == substitutions_->cend()) {
      unify_by_substitution();
      return;
    }
    try {
      orig_r_ = compute_single_substitution(r, it->second, max_id_r_);
    } catch (UnificationError& e) {
      e.add_context(orig_l_, orig_r_);
      throw;
    }
    orig_r_->accept(*this);
  }

  void visit(const TupleType&) override { unify_by_substitution(); }

  void visit(const RecordType&) override { unify_by_substitution(); }

  void visit(const FunctionType&) override { unify_by_substitution(); }

  void visit(const ConstructedType&) override { unify_by_substitution(); }

 private:
  const UndeterminedType& l_;
  TypePtr orig_l_;
  TypePtr orig_r_;
  Substitutions& substitutions_;
  std::uint64_t max_id_l_;
  std::uint64_t max_id_r_;

  void unify_by_substitution() {
    try {
      result.unified_type = compute_single_substitution(l_, orig_r_, max_id_l_);
    } catch (UnificationError& e) {
      e.add_context(orig_l_, orig_r_);
      throw;
    }
    add_substitution(substitutions_, result.new_substitutions, l_, orig_r_);
  }
};

/** Performs unification when l is a tuple type. */
class TupleUnifier : public UnifierBase {
 public:
  TupleUnifier(const TupleType& l, TypePtr orig_l, TypePtr orig_r,
               Substitutions& substitutions, std::uint64_t max_id_l,
               std::uint64_t max_id_r)
      : UnifierBase("tuple type", std::move(orig_l), std::move(orig_r),
                    substitutions, max_id_r),
        l_(l),
        max_id_l_(max_id_l) {}

  void visit(const TupleType& r) override {
    if (l_.types()->size() != r.types()->size()) {
      throw UnificationError("Cannot unify tuples of different length",
                             orig_l(), orig_r());
    }
    auto subtypes = unify_subtypes(l_.types(), r.types(), substitutions(),
                                   max_id_l_, max_id_r());
    result.unified_type = make_managed<TupleType>(subtypes.unified_subtypes);
    result.new_substitutions =
        result.new_substitutions | subtypes.new_substitutions;
  }

 private:
  const TupleType& l_;
  const std::uint64_t max_id_l_;
};

/** Performs unification when l is a record type. */
class RecordUnifier : public UnifierBase {
 public:
  RecordUnifier(const RecordType& l, TypePtr orig_l, TypePtr orig_r,
                Substitutions& substitutions, std::uint64_t max_id_l,
                std::uint64_t max_id_r)
      : UnifierBase("record type", std::move(orig_l), std::move(orig_r),
                    substitutions, max_id_r),
        l_(l),
        max_id_l_(max_id_l) {}

  // To merge two record types:
  //
  // 1. If r doesn't have a wildcard (...), l can't have any row labels r
  // doesn't have. Otherwise, all of the rows with labels not in r are in the
  // unified type.
  //
  // 2. If l doesn't have a wildcard, r can't have any row labels l doesn't
  // have. Otherwise, all of the rows with labels not in l are in the unified
  // type.
  //
  // 3. For all rows with labels shared by both l and r, the unified
  // type contains a row with that label and the type resulting from
  // unifying the types in l and r.
  //
  // 4. Iff both l and r have a wild card, the unified type has a
  // wildcard.
  void visit(const RecordType& r) override {
    const auto l_only = l_.rows() - r.rows();
    if (!l_only->empty() && !r.has_wildcard()) {
      throw UnificationError("Cannot unify record types without a wildcard.",
                             orig_l(), orig_r());
    }
    const auto r_only = r.rows() - l_.rows();
    if (!r_only->empty() && !l_.has_wildcard()) {
      throw UnificationError("Cannot unify record types without a wildcard.",
                             orig_l(), orig_r());
    }
    auto rows = collections::managed_map<ManagedString, Type>({});
    const auto max_id_u = std::min(max_id_l_, max_id_r());
    // Order is important: `both` has the values from `r`.
    const auto both = l_.rows() & r.rows();
    std::vector<StringPtr> keys;
    keys.reserve(both->size());
    for (const auto& entry : *both) {
      auto u = unify(*l_.rows()->get(*entry.first), entry.second,
                     substitutions(), max_id_l_, max_id_r());
      rows = rows->insert(entry.first, u.unified_type).first;
      result.new_substitutions = result.new_substitutions | u.new_substitutions;
      for (const auto& k : keys) {
        rows =
            rows->insert(k, apply_substitutions(*rows->get(*k),
                                                u.new_substitutions, max_id_u))
                .first;
      }
      keys.push_back(entry.first);
    }
    result.unified_type = make_managed<RecordType>(
        rows | l_only | r_only, r.has_wildcard() && l_.has_wildcard());
  }

 private:
  const RecordType& l_;
  const std::uint64_t max_id_l_;
};

/** Performs unification when l is a function type. */
class FunctionUnifier : public UnifierBase {
 public:
  FunctionUnifier(const FunctionType& l, TypePtr orig_l, TypePtr orig_r,
                  Substitutions& substitutions, std::uint64_t max_id_l,
                  std::uint64_t max_id_r)
      : UnifierBase("function type", std::move(orig_l), std::move(orig_r),
                    substitutions, max_id_r),
        l_(l),
        max_id_l_(max_id_l) {}

  void visit(const FunctionType& r) override {
    const auto max_id_u = std::min(max_id_l_, max_id_r());
    auto param_u =
        unify(l_.param(), r.param(), substitutions(), max_id_l_, max_id_r());
    auto result_u =
        unify(l_.result(), r.result(), substitutions(), max_id_l_, max_id_r());
    result.unified_type = make_managed<FunctionType>(
        apply_substitutions(param_u.unified_type, result_u.new_substitutions,
                            max_id_u),
        result_u.unified_type);
    result.new_substitutions = result.new_substitutions |
                               param_u.new_substitutions |
                               result_u.new_substitutions;
  }

 private:
  const FunctionType& l_;
  const std::uint64_t max_id_l_;
};

/** Performs unification when l is a constructed type. */
class ConstructedUnifier : public UnifierBase {
 public:
  ConstructedUnifier(const ConstructedType& l, TypePtr orig_l, TypePtr orig_r,
                     Substitutions& substitutions, std::uint64_t max_id_l,
                     std::uint64_t max_id_r)
      : UnifierBase("constructed type", std::move(orig_l), std::move(orig_r),
                    substitutions, max_id_r),
        l_(l),
        max_id_l_(max_id_l) {}

  void visit(const ConstructedType& r) override {
    if (l_.name()->stamp() != r.name()->stamp()) {
      throw UnificationError("Cannot unify distinct constructed types",
                             orig_l(), orig_r());
    }
    assert(l_.types()->size() == l_.name()->arity());
    assert(l_.types()->size() == r.types()->size());
    auto subtypes = unify_subtypes(l_.types(), r.types(), substitutions(),
                                   max_id_l_, max_id_r());
    result.unified_type =
        make_managed<ConstructedType>(l_.name(), subtypes.unified_subtypes);
    result.new_substitutions =
        result.new_substitutions | subtypes.new_substitutions;
  }

 private:
  const ConstructedType& l_;
  const std::uint64_t max_id_l_;
};

/**
 * Unifies l and r.
 *
 * This is the first step in the double-dispatch approach. It visits `l` to
 * determine its type and then (usually) dispatches to the appropriate visitor
 * to visit `r`.
 */
class UnifyDispatcher : public TypeVisitor {
 public:
  unification_t result;

  UnifyDispatcher(TypePtr l, TypePtr r, Substitutions& substitutions,
                  std::uint64_t maximum_type_name_id_l,
                  std::uint64_t maximum_type_name_id_r)
      : orig_l_(std::move(l)),
        orig_r_(std::move(r)),
        substitutions_(substitutions),
        max_id_l_(maximum_type_name_id_l),
        max_id_r_(maximum_type_name_id_r) {}

  void visit(const TypeWithAgeRestriction& l) override {
    orig_l_ = l.type();
    max_id_l_ = std::min(max_id_l_, l.birthdate());
    orig_l_->accept(*this);
    assert(result.unified_type->id_of_youngest_typename() < l.birthdate());
    if (!result.unified_type->undetermined_types()->empty()) {
      result.unified_type = make_managed<TypeWithAgeRestriction>(
          result.unified_type, l.birthdate());
    }
  }

  void visit(const TypeVar& l) override {
    TypeVarUnifier u{l, orig_l_, orig_r_, substitutions_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

  void visit(const UndeterminedType& l) override {
    const auto it = substitutions_->find(*l.stamp());
    if (it != substitutions_->cend()) {
      try {
        orig_l_ = compute_single_substitution(l, it->second, max_id_l_);
      } catch (UnificationError& e) {
        e.add_context(orig_l_, orig_r_);
        throw;
      }
      orig_l_->accept(*this);
      return;
    }
    UndeterminedUnifier u{l,         orig_l_,  orig_r_, substitutions_,
                          max_id_l_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

  void visit(const TupleType& l) override {
    TupleUnifier u{l, orig_l_, orig_r_, substitutions_, max_id_l_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

  void visit(const RecordType& l) override {
    RecordUnifier u{l, orig_l_, orig_r_, substitutions_, max_id_l_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

  void visit(const FunctionType& l) override {
    FunctionUnifier u{l,         orig_l_,  orig_r_, substitutions_,
                      max_id_l_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

  void visit(const ConstructedType& l) override {
    ConstructedUnifier u{l,         orig_l_,  orig_r_, substitutions_,
                         max_id_l_, max_id_r_};
    orig_r_->accept(u);
    result = std::move(u.result);
  }

 private:
  TypePtr orig_l_;
  TypePtr orig_r_;
  Substitutions& substitutions_;
  std::uint64_t max_id_l_;
  std::uint64_t max_id_r_;
};

}  // namespace

/**
 * Implementation note: The general approach is through double
 * dispatch. First the UnifyDispatcher visitor determines the type of
 * l. In most cases, it creates a second visitor of the appropriate
 * subclass of UnifierBase, which visits r to determine its type and
 * unify it appropriately.
 */
unification_t unify(TypePtr l, TypePtr r, Substitutions& substitutions,
                    std::uint64_t maximum_type_name_id_l,
                    std::uint64_t maximum_type_name_id_r) {
  UnifyDispatcher u{l, std::move(r), substitutions, maximum_type_name_id_l,
                    maximum_type_name_id_r};
  l->accept(u);
  return std::move(u.result);
}

unification_t unify(TypeList types, Substitutions& substitutions,
                    std::uint64_t maximum_type_name_id,
                    managed_ptr<Stamp> fresh_stamp) {
  unification_t result;
  result.unified_type = make_managed<UndeterminedType>(std::move(fresh_stamp));
  for (std::size_t i = 0; i < types->size(); ++i) {
    auto u = unify(result.unified_type, (*types)[i], substitutions,
                   maximum_type_name_id, maximum_type_name_id);
    result.unified_type = u.unified_type;
    result.new_substitutions = result.new_substitutions | u.new_substitutions;
  }
  return result;
}

subtype_unification_t unify_subtypes(TypeList ls, TypeList rs,
                                     Substitutions& substitutions,
                                     std::uint64_t maximum_type_name_id_l,
                                     std::uint64_t maximum_type_name_id_r) {
  assert(ls->size() == rs->size());
  subtype_unification_t result;
  result.unified_subtypes =
      make_managed<collections::ManagedArray<Type>>(ls->size());
  if (ls->empty()) return result;
  const auto max_id_u =
      std::min(maximum_type_name_id_l, maximum_type_name_id_r);
  for (std::size_t i = 0; i < ls->size(); ++i) {
    auto u = unify((*ls)[i], (*rs)[i], substitutions, maximum_type_name_id_l,
                   maximum_type_name_id_r);
    (*result.unified_subtypes)[i] = u.unified_type;
    result.new_substitutions = result.new_substitutions | u.new_substitutions;
    // We have to apply the new substitutions to everything already unified.
    for (std::size_t j = 0; j < i; ++j) {
      (*result.unified_subtypes)[j] = apply_substitutions(
          (*result.unified_subtypes)[j], u.new_substitutions, max_id_u);
    }
  }
  return result;
}

}  // namespace emil::typing
