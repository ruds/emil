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

#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <type_traits>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/string.h"

/**
 * @file types.h
 *
 * @brief Provides types and functionality used when doing static type
 * analysis on emil programs.
 *
 * Objects in the `TypeObj` hierarchy are managed by the runtime
 * since, in general, they will stick around for static type analysis
 * of further top-level declarations. This hierarchy closely follows
 * the static semantic objects described in Chapters 4 and 5 of the
 * Definition of Standard ML (Revised).
 */

namespace emil {
class Typer;
}

namespace emil::typing {

class TypeObj;

template <typename T>
concept TypeObjType = std::is_base_of<TypeObj, T>::value;

using StringSet = collections::SetPtr<ManagedString>;

template <TypeObjType T>
using StringMap = collections::MapPtr<ManagedString, T>;

/**
 * @brief A "timestamp" for type names and undetermined types.
 *
 * All types are given a unique typename, which e.g. prevents errors
 * when a type constructor is bound to a new type. During type unification, it
 * is important that unknown types are not unified with types that are defined
 * later. For example, the following snippet must not typecheck:
 *
 * @code
 * let
 *     val r = ref NONE
 *     datatype t = C
 * in
 *     r := SOME C
 * end
 * @endcode
 *
 * `Stamp` facilitates this by allowing the typer to assign a
 * monotonically increasing id to each type name and undetermined
 * type. This stamp is propagated to subterms during unification, and
 * unification of a type name with an "older" undetermined type is
 * forbidden.
 *
 * This idea is described by Andreas Rossberg in "HaMLet S: To Become Or Not To
 * Become Successor ML :-)".
 */
class Stamp : public Managed {
 public:
  struct token {
   private:
    token() {}
    friend class StampGenerator;
  };

  Stamp(token, std::uint64_t id);

  std::uint64_t id() const { return id_; }

 private:
  const std::uint64_t id_;

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override { return sizeof(Stamp); }
};

bool operator<(const Stamp& l, const Stamp& r);
bool operator<(std::uint64_t l, const Stamp& r);
bool operator<(const Stamp& l, std::uint64_t r);

using StampSet = collections::SetPtr<Stamp>;

class StampGenerator {
 public:
  managed_ptr<Stamp> operator()();

 private:
  friend class emil::Typer;

  std::uint64_t next_id_ = 1;

  StampGenerator();
  StampGenerator(const StampGenerator&) = delete;
  StampGenerator& operator=(const StampGenerator&) = delete;
  StampGenerator(StampGenerator&&) = delete;
  StampGenerator& operator=(StampGenerator&&) = delete;
};

/**
 * @brief Objects that describe types and collections of types.
 *
 * These are the same as the "semantic objects" described in the Definition.
 */
class TypeObj : public Managed {
 public:
  const StringSet& free_variables() const { return free_variables_; }
  const StampSet& type_names() const { return type_names_; }

 protected:
  TypeObj(StringSet free_variables, StampSet type_names);
  ~TypeObj() override;

 private:
  const StringSet free_variables_;
  const StampSet type_names_;

  virtual void visit_additional_subobjects(const ManagedVisitor& visitor) = 0;

  void visit_subobjects(const ManagedVisitor& visitor) final;
};

class Type : public TypeObj {
 protected:
  using TypeObj::TypeObj;
};
using TypePtr = managed_ptr<Type>;
using TypeList = collections::ArrayPtr<Type>;

/** A type variable explicitly present in the code. */
class TypeVar : public Type {
 public:
  explicit TypeVar(std::u8string_view name);
  explicit TypeVar(StringPtr name);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }

  void visit_additional_subobjects(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override { return sizeof(TypeVar); }

 private:
  StringPtr name_;
};

/** An as-yet undetermined type, produced during type inference. */
class UndeterminedType : public Type {
 public:
  UndeterminedType(std::u8string_view name, managed_ptr<Stamp> stamp);
  UndeterminedType(StringPtr name, managed_ptr<Stamp> stamp);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }
  const managed_ptr<Stamp>& stamp() const { return stamp_; }

  void visit_additional_subobjects(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(UndeterminedType);
  }

 private:
  StringPtr name_;
  managed_ptr<Stamp> stamp_;
};

/** A globally unique name assigned to a constructed type. */
class TypeName : public TypeObj {
 public:
  TypeName(std::u8string_view name, managed_ptr<Stamp> stamp,
           std::size_t arity);
  TypeName(StringPtr name, managed_ptr<Stamp> stamp, std::size_t arity);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }
  const managed_ptr<Stamp>& stamp() const { return stamp_; }
  std::size_t arity() const { return arity_; }

 private:
  StringPtr name_;
  managed_ptr<Stamp> stamp_;
  const std::size_t arity_;

  void visit_additional_subobjects(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeName);
  }
};

/** A tuple of the given types. */
class TupleType : public Type {
 public:
  explicit TupleType(TypeList types);

  TypeList types() const { return types_; }

 private:
  TypeList types_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TupleType);
  }
};

/** A mapping from labels to types. */
class RecordType : public Type {
 public:
  explicit RecordType(StringMap<Type> rows);

  StringMap<Type> rows() const { return rows_; }

 private:
  StringMap<Type> rows_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(RecordType);
  }
};

/** The type of a function object. */
class FunctionType : public Type {
 public:
  FunctionType(TypePtr param, TypePtr result);

  TypePtr param() const { return param_; }
  TypePtr result() const { return result_; }

 private:
  const TypePtr param_;
  const TypePtr result_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(FunctionType);
  }
};

/** A constructed type: a type constructor and its type parameters. */
class ConstructedType : public Type {
 public:
  ConstructedType(managed_ptr<TypeName> name, TypeList types);

  std::u8string_view name_str() const { return name_->name(); }
  managed_ptr<TypeName> name() const { return name_; }
  const TypeList& types() const { return types_; }

 private:
  managed_ptr<TypeName> name_;
  const TypeList types_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ConstructedType);
  }
};

class BuiltinTypes : public TypeObj {
 public:
  static BuiltinTypes create(StampGenerator& g);

  TypePtr bigint_type() const { return bi_; }
  TypePtr int_type() const { return i_; }
  TypePtr byte_type() const { return by_; }
  TypePtr float_type() const { return fl_; }
  TypePtr bool_type() const { return bo_; }
  TypePtr char_type() const { return c_; }
  TypePtr string_type() const { return s_; }
  TypePtr tuple_type(TypeList types) const;
  TypePtr list_type(TypePtr type) const;
  TypePtr record_type(StringMap<Type> rows) const;

 private:
  const TypePtr bi_;
  const TypePtr i_;
  const TypePtr by_;
  const TypePtr fl_;
  const TypePtr bo_;
  const TypePtr c_;
  const TypePtr s_;
  const managed_ptr<TypeName> l_;

  BuiltinTypes(managed_ptr<Stamp> bi, managed_ptr<Stamp> i,
               managed_ptr<Stamp> by, managed_ptr<Stamp> fl,
               managed_ptr<Stamp> bo, managed_ptr<Stamp> c,
               managed_ptr<Stamp> s, managed_ptr<Stamp> l);

  void visit_additional_subobjects(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(BuiltinTypes);
  }
};

/** All bound identifiers are associated with one of these statuses. */
enum class IdStatus {
  Exception,
  Variable,
  Constructor,
};

/**
 * @brief A mapping from type variables to a type.
 *
 * A `TypeFunction` binds its variables (which must be distinct). That
 * is, the free variables of a type function are the free variables of
 * the resulting type expression *excluding the bound variables*.
 */
class TypeFunction : public TypeObj {
 public:
  TypeFunction(TypePtr t, collections::ArrayPtr<TypeVar> bound);

  TypePtr t() const { return t_; }
  const collections::ArrayPtr<TypeVar>& bound() const { return bound_; }

 private:
  const TypePtr t_;
  const collections::ArrayPtr<TypeVar> bound_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeFunction);
  }
};

/**
 * @brief A particular generalization of a type.
 *
 * A type scheme is a generalization of a type using a universal
 * quantifier: ∀ɑ1,ɑ2,...,ɑk τ. The free variables of a type scheme
 * are the free variables of the type excluding the quantified
 * variables.
 */
class TypeScheme : public TypeObj {
 public:
  TypeScheme(TypePtr t, collections::ArrayPtr<TypeVar> bound);

  TypePtr t() const { return t_; }
  const collections::ArrayPtr<TypeVar>& bound() const { return bound_; }

 private:
  const TypePtr t_;
  const collections::ArrayPtr<TypeVar> bound_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeScheme);
  }
};

class ValEnv;

/**
 * @brief The type structure that a type constructor is bound to.
 *
 * A type structure is only well-formed if `env` is empty or `fn` is
 * (∀ɑ1,ɑ2,...,ɑk t) for some TypeName t.
 */
class TypeStructure : public TypeObj {
 public:
  TypeStructure(managed_ptr<TypeFunction> fn, managed_ptr<ValEnv> env);

  const managed_ptr<TypeFunction>& fn() const { return fn_; }
  const managed_ptr<ValEnv>& env() const { return env_; }

 private:
  const managed_ptr<TypeFunction> fn_;
  const managed_ptr<ValEnv> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeStructure);
  }
};

/** The mapping between type constructor names and type structures in an
 * environment. */
class TypeEnv : public TypeObj {
 public:
  explicit TypeEnv(StringMap<TypeStructure> env);

  std::optional<managed_ptr<TypeStructure>> get(
      const std::u8string_view& key) const;

  const StringMap<TypeStructure>& env() const { return env_; }

 private:
  StringMap<TypeStructure> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(TypeEnv); }
};

/** The type scheme and identifier status associated with a value variable in an
 * environment. */
class ValueBinding : public TypeObj {
 public:
  ValueBinding(managed_ptr<TypeScheme> scheme, IdStatus status);

  managed_ptr<TypeScheme> scheme() const { return scheme_; }
  IdStatus status() const { return status_; }

 private:
  const managed_ptr<TypeScheme> scheme_;
  const IdStatus status_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ValueBinding);
  }
};

/** The mapping from value variable identifiers to their value bindings. */
class ValEnv : public TypeObj {
 public:
  explicit ValEnv(StringMap<ValueBinding> env);

  std::optional<managed_ptr<ValueBinding>> get(
      const std::u8string_view& key) const;

  const StringMap<ValueBinding>& env() const { return env_; }

 private:
  StringMap<ValueBinding> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(ValEnv); }
};

/** The type environment of a program. */
class Env : public TypeObj {
 public:
  Env(managed_ptr<TypeEnv> type_env, managed_ptr<ValEnv> val_env);

  managed_ptr<TypeEnv> type_env() const { return type_env_; }
  managed_ptr<ValEnv> val_env() const { return val_env_; }

 private:
  const managed_ptr<TypeEnv> type_env_;
  const managed_ptr<ValEnv> val_env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(Env); }
};

/** The type context of a program. */
class Context : public TypeObj {
 public:
  Context(StampSet type_names, StringSet explicit_type_variables,
          managed_ptr<Env> env);

  const StringSet& explicit_type_variables() const { return vars_; }
  const managed_ptr<Env>& env() const { return env_; }

 private:
  const StringSet vars_;
  const managed_ptr<Env> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(Context); }
};

/** The type basis of a program. */
class Basis : public TypeObj {
 public:
  Basis(StampSet type_names, managed_ptr<Env> env);

  const managed_ptr<Env>& env() const { return env_; }

  managed_ptr<Context> as_context() const;

 private:
  const managed_ptr<Env> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(Basis); }
};

managed_ptr<TypeEnv> operator+(const managed_ptr<TypeEnv>& l,
                               const managed_ptr<TypeEnv>& r);
managed_ptr<ValEnv> operator+(const managed_ptr<ValEnv>& l,
                              const managed_ptr<ValEnv>& r);
managed_ptr<Env> operator+(const managed_ptr<Env>& l,
                           const managed_ptr<Env>& r);

managed_ptr<Basis> operator+(const managed_ptr<Basis>& B,
                             const managed_ptr<Env>& E);

}  // namespace emil::typing
