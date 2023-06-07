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
#include <exception>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

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

bool operator==(const Stamp& l, const Stamp& r);
bool operator==(std::uint64_t l, const Stamp& r);
bool operator==(const Stamp& l, std::uint64_t r);

bool operator!=(const Stamp& l, const Stamp& r);
bool operator!=(std::uint64_t l, const Stamp& r);
bool operator!=(const Stamp& l, std::uint64_t r);

bool operator<(const Stamp& l, const Stamp& r);
bool operator<(std::uint64_t l, const Stamp& r);
bool operator<(const Stamp& l, std::uint64_t r);

using StampSet = collections::SetPtr<Stamp>;

class StampGenerator {
 public:
  StampGenerator();

  managed_ptr<Stamp> operator()();

 private:
  std::uint64_t next_id_ = 1;

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

class TypeWithAgeRestriction;
class TypeVar;
class UndeterminedType;
class TupleType;
class RecordType;
class FunctionType;
class ConstructedType;

class TypeVisitor {
 public:
  virtual ~TypeVisitor();
  virtual void visit(const TypeWithAgeRestriction& t) = 0;
  virtual void visit(const TypeVar& t) = 0;
  virtual void visit(const UndeterminedType& t) = 0;
  virtual void visit(const TupleType& t) = 0;
  virtual void visit(const RecordType& t) = 0;
  virtual void visit(const FunctionType& t) = 0;
  virtual void visit(const ConstructedType& t) = 0;
};

class Type : public TypeObj {
 public:
  /**
   * The id of the youngest typename used by this type, or 0 if there are no
   * typenames.
   *
   * The inference algorithm requires that no undetermined type unify
   * with a type containing a younger typename.
   */
  std::uint64_t id_of_youngest_typename() const {
    return id_of_youngest_typename_;
  }

  const StampSet& undetermined_types() const { return undetermined_types_; }

  virtual void accept(TypeVisitor& v) const = 0;

 protected:
  Type(StringSet free_variables, StampSet undetermined_types,
       StampSet type_names);

 private:
  const std::uint64_t id_of_youngest_typename_;
  const StampSet undetermined_types_;

  virtual void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) = 0;

  void visit_additional_subobjects(const ManagedVisitor& visitor) final;
};
using TypePtr = managed_ptr<Type>;
using TypeList = collections::ArrayPtr<Type>;
using Substitutions = collections::MapPtr<Stamp, Type>;

/**
 * A wrapper for a type that is used to propagate age restrictions into
 * subtypes.
 *
 * When an undetermined type '~N is substituted by a type that has
 * undetermined types in its subtypes, it is important that none of
 * those types is later substitued by a type containing a typename
 * younger than '~N.
 */
class TypeWithAgeRestriction : public Type {
 public:
  TypeWithAgeRestriction(TypePtr type, std::uint64_t birthdate);

  const TypePtr& type() const { return type_; }
  std::uint64_t birthdate() const { return birthdate_; }

  void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeWithAgeRestriction);
  }

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const TypePtr type_;
  const std::uint64_t birthdate_;
};

/** A type variable explicitly present in the code. */
class TypeVar : public Type {
 public:
  explicit TypeVar(std::u8string_view name);
  explicit TypeVar(StringPtr name);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }

  void visit_additional_subobjects_of_type(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override { return sizeof(TypeVar); }

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const StringPtr name_;
};

/** An as-yet undetermined type, produced during type inference. */
class UndeterminedType : public Type {
 public:
  explicit UndeterminedType(managed_ptr<Stamp> stamp);
  explicit UndeterminedType(StampGenerator& stamper);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }
  const managed_ptr<Stamp>& stamp() const { return stamp_; }

  void visit_additional_subobjects_of_type(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(UndeterminedType);
  }

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const StringPtr name_;
  const managed_ptr<Stamp> stamp_;
};

inline const std::size_t INFINITE_SPAN =
    std::numeric_limits<std::size_t>::max();

/** A globally unique name assigned to a constructed type. */
class TypeName : public TypeObj {
 public:
  TypeName(std::u8string_view name, managed_ptr<Stamp> stamp, std::size_t arity,
           std::size_t span);
  TypeName(std::u8string_view name, StampGenerator& stamper, std::size_t arity,
           std::size_t span);
  TypeName(StringPtr name, managed_ptr<Stamp> stamp, std::size_t arity,
           std::size_t span);
  TypeName(StringPtr name, StampGenerator& stamper, std::size_t arity,
           std::size_t span);

  std::u8string_view name() const { return *name_; }
  StringPtr name_ptr() const { return name_; }
  const managed_ptr<Stamp>& stamp() const { return stamp_; }
  /** The number of type parameters needed to construct a type with this name.
   */
  std::size_t arity() const { return arity_; }
  /**
   * The number of value constructors this type has.
   *
   * May be INFINITE_SPAN (e.g. int, float, string, and bigint).
   */
  std::size_t span() const { return span_; }

 private:
  const StringPtr name_;
  const managed_ptr<Stamp> stamp_;
  const std::size_t arity_;
  const std::size_t span_;

  void visit_additional_subobjects(const ManagedVisitor&) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TypeName);
  }
};

/** A tuple of the given types. */
class TupleType : public Type {
 public:
  explicit TupleType(TypeList types);

  const TypeList& types() const { return types_; }

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const TypeList types_;

  void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TupleType);
  }
};

/** A mapping from labels to types. */
class RecordType : public Type {
 public:
  explicit RecordType(StringMap<Type> rows, bool has_wildcard = false);

  StringMap<Type> rows() const { return rows_; }
  bool has_wildcard() const { return has_wildcard_; }

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const StringMap<Type> rows_;
  const bool has_wildcard_;

  void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) override;
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

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  const TypePtr param_;
  const TypePtr result_;

  void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) override;
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

  void accept(TypeVisitor& v) const override { v.visit(*this); }

 private:
  managed_ptr<TypeName> name_;
  const TypeList types_;

  void visit_additional_subobjects_of_type(
      const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ConstructedType);
  }
};

class BuiltinTypes : public TypeObj {
 public:
  static BuiltinTypes create(StampGenerator& g);

  /** Type constructors from the initial basis. */
  static constexpr std::u8string_view TRUE = u8"true";
  static constexpr std::u8string_view FALSE = u8"false";
  static constexpr std::u8string_view NIL = u8"nil";
  static constexpr std::u8string_view CONS = u8"(::)";
  static constexpr std::u8string_view REF = u8"ref";

  managed_ptr<ConstructedType> bigint_type() const { return bi_; }
  managed_ptr<ConstructedType> int_type() const { return i_; }
  managed_ptr<ConstructedType> byte_type() const { return by_; }
  managed_ptr<ConstructedType> float_type() const { return fl_; }
  managed_ptr<ConstructedType> bool_type() const { return bo_; }
  managed_ptr<ConstructedType> char_type() const { return c_; }
  managed_ptr<ConstructedType> string_type() const { return s_; }
  // cppcheck-suppress functionStatic
  TypePtr tuple_type(TypeList types) const;
  managed_ptr<ConstructedType> list_type(TypePtr type) const;
  managed_ptr<TypeName> list_name() const { return l_; }
  managed_ptr<ConstructedType> ref_type(TypePtr type) const;
  managed_ptr<TypeName> ref_name() const { return r_; }
  // cppcheck-suppress functionStatic
  TypePtr record_type(StringMap<Type> rows) const;

 private:
  const managed_ptr<ConstructedType> bi_;
  const managed_ptr<ConstructedType> i_;
  const managed_ptr<ConstructedType> by_;
  const managed_ptr<ConstructedType> fl_;
  const managed_ptr<ConstructedType> bo_;
  const managed_ptr<ConstructedType> c_;
  const managed_ptr<ConstructedType> s_;
  const managed_ptr<TypeName> l_;
  const managed_ptr<TypeName> r_;

  BuiltinTypes(managed_ptr<Stamp> bi, managed_ptr<Stamp> i,
               managed_ptr<Stamp> by, managed_ptr<Stamp> fl,
               managed_ptr<Stamp> bo, managed_ptr<Stamp> c,
               managed_ptr<Stamp> s, managed_ptr<Stamp> l,
               managed_ptr<Stamp> r);

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
 *
 * Notationally, this can be written θ = Λα.τ, where each of the
 * variables of α is distinct from the others and free in τ.
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

  /**
   * Instantiates this type scheme.
   *
   * Returns a fresh type with bound variables mapped to undetermined
   * types.
   */
  TypePtr instantiate(StampGenerator& stamper) const;

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
 * (Λɑ1,ɑ2,...,ɑk.t) for some TypeName t with arity k.
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

  std::optional<managed_ptr<TypeStructure>> get(std::u8string_view key) const;

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

/**
 * Canonicalizes the name of a value identifier.
 *
 * Infix operators, prefix operators, and other value identifiers do not share a
 * namespace. This function applies a canonical renaming to `id` so that they
 * can share the same map.
 */
std::u8string canonicalize_val_id(std::u8string_view id, bool is_op,
                                  bool is_prefix_op);

class BindingError : public std::exception {
 public:
  std::u8string id;

  explicit BindingError(std::u8string_view id);

  const char* what() const noexcept override { return full_msg_.c_str(); }

 private:
  std::string full_msg_;
};

/** The mapping from value variable identifiers to their value bindings. */
class ValEnv : public TypeObj {
 public:
  explicit ValEnv(StringMap<ValueBinding> env);

  std::optional<managed_ptr<ValueBinding>> get(std::u8string_view key) const;

  /**
   * Binds `id` with the given type scheme and status.
   *
   * If allow_rebinding is false, throw BindingError if id was already bound in
   * this environment.
   */
  managed_ptr<ValEnv> add_binding(std::u8string_view id,
                                  managed_ptr<TypeScheme> scheme,
                                  IdStatus status, bool allow_rebinding) const;

  /** Apply the given substitutions to each binding's type scheme. */
  managed_ptr<ValEnv> apply_substitutions(Substitutions subs) const;

  const StringMap<ValueBinding>& env() const { return env_; }

 private:
  StringMap<ValueBinding> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(ValEnv); }
};

class StrEnv;

/** The type environment of a program. */
class Env : public TypeObj {
 public:
  Env(managed_ptr<StrEnv> str_env, managed_ptr<TypeEnv> type_env,
      managed_ptr<ValEnv> val_env);

  std::optional<managed_ptr<ValueBinding>> lookup_val(
      const std::vector<std::u8string>& qualifiers,
      std::u8string_view id) const;

  managed_ptr<StrEnv> str_env() const;
  managed_ptr<TypeEnv> type_env() const { return type_env_; }
  managed_ptr<ValEnv> val_env() const { return val_env_; }

 private:
  const managed_ptr<StrEnv> str_env_;
  const managed_ptr<TypeEnv> type_env_;
  const managed_ptr<ValEnv> val_env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(Env); }
};

/**
 * The mapping between structure ids and structures in an environment.
 */
class StrEnv : public TypeObj {
 public:
  explicit StrEnv(StringMap<Env> env);

  std::optional<managed_ptr<Env>> get(std::u8string_view key) const;

  const StringMap<Env>& env() const { return env_; }

 private:
  StringMap<Env> env_;

  void visit_additional_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(StrEnv); }
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

managed_ptr<StrEnv> operator+(const managed_ptr<StrEnv>& l,
                              const managed_ptr<StrEnv>& r);
managed_ptr<TypeEnv> operator+(const managed_ptr<TypeEnv>& l,
                               const managed_ptr<TypeEnv>& r);
managed_ptr<ValEnv> operator+(const managed_ptr<ValEnv>& l,
                              const managed_ptr<ValEnv>& r);
managed_ptr<Env> operator+(const managed_ptr<Env>& l,
                           const managed_ptr<Env>& r);
managed_ptr<Context> operator+(const managed_ptr<Context>& C,
                               const managed_ptr<Env>& E);

managed_ptr<Basis> operator+(const managed_ptr<Basis>& B,
                             const managed_ptr<Env>& E);

enum class CanonicalizeUndeterminedTypes {
  NO,
  YES,
};

/**
 * Prints a type to string.
 *
 * If c is YES, undetermined types are renamed to '~0, '~1, etc. based
 * on their order of appearance in the string.
 */
std::u8string print_type(TypePtr t, CanonicalizeUndeterminedTypes c =
                                        CanonicalizeUndeterminedTypes::NO);
std::u8string print_type(const Type& t, CanonicalizeUndeterminedTypes c =
                                            CanonicalizeUndeterminedTypes::NO);

class UnificationError : public std::exception {
 public:
  explicit UnificationError(const std::string& msg);
  UnificationError(const std::string& msg, TypePtr l, TypePtr r);

  const char* what() const noexcept override { return full_msg_.c_str(); }

  /** Returns the types being unified from most specific subtype to most general
   * type. */
  const std::vector<std::pair<TypePtr, TypePtr>>& context() const {
    return context_;
  }

  /** Used to add context during stack unwinding. */
  void add_context(TypePtr l, TypePtr r);

 private:
  MemoryManager::hold hold_;
  std::vector<std::pair<TypePtr, TypePtr>> context_;
  std::string full_msg_;
};

inline constexpr std::uint64_t NO_ADDITIONAL_TYPE_NAME_RESTRICTION =
    std::numeric_limits<std::uint64_t>::max();

/**
 * Apply the given substitutions to the given type.
 *
 * Throws a UnificationError if an illegal substitution is attempted (i.e. a
 * too-young typename is substituted for an older undetermined type).
 */
TypePtr apply_substitutions(
    TypePtr t, Substitutions substitutions,
    std::uint64_t maximum_type_name_id = NO_ADDITIONAL_TYPE_NAME_RESTRICTION);

/**
 * The result of a unification.
 */
struct unification_t {
  // The type resulting from the unification.
  TypePtr unified_type;
  // New substitutions deduced during the unification.
  Substitutions new_substitutions = collections::managed_map<Stamp, Type>({});
};

/**
 * Unify l and r to a single type.
 *
 * The given substitutions are applied to l and r before unifying. New
 * substitutions deduced while unifying l and r are added to
 * substitutions as well as being returned separately in the result's
 * new_substitutions field.
 *
 * Throws a UnificationError if the types cannot be unified.
 */
unification_t unify(TypePtr l, TypePtr r, Substitutions& substitutions,
                    std::uint64_t maximum_type_name_id_l,
                    std::uint64_t maximum_type_name_id_r);

/**
 * Unify all the types to a single type.
 *
 * The given substitutions are applied to each type before unifying. New
 * substitutions deduced while unifying are added to substitutions as well as
 * being returned separately in the result's new_substitutions field.
 *
 * Throws a UnificationError if the types cannot be unified.
 */
unification_t unify(TypeList types, Substitutions& substitutions,
                    std::uint64_t maximum_type_name_id,
                    managed_ptr<Stamp> fresh_stamp);

struct subtype_unification_t {
  TypeList unified_subtypes;
  Substitutions new_substitutions = collections::managed_map<Stamp, Type>({});
};

/**
 * Unify the types in ls and rs in a pairwise fashion.
 *
 * The given substitutions are applied to each type before unifying.
 * New substitutions deduced while unifying are added to substitutions
 * as well as being returned separately in the result's
 * new_substitutions field.
 *
 * Throws a UnificationError if any pair of types cannot be unified.
 */
subtype_unification_t unify_subtypes(TypeList ls, TypeList rs,
                                     Substitutions& substitutions,
                                     std::uint64_t maximum_type_name_id_l,
                                     std::uint64_t maximum_type_name_id_r);

}  // namespace emil::typing
