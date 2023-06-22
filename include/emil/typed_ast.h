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
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/types.h"

/**
 * @file typed_ast.h
 *
 * @brief Provides classes for an abstract syntax tree annotated with types.
 */

namespace emil {

class bigint;
class TDecl;

/** Describes how to access parts of a value to bind to identifiers. */
struct bind_rule_t : public Managed {
  // bind the current value to these names
  collections::ConsPtr<ManagedString> names;

  struct record_field_access_t : public Managed {
    StringPtr field_name;
    managed_ptr<bind_rule_t> rule;

    record_field_access_t(StringPtr field_name, managed_ptr<bind_rule_t> rule)
        : field_name(field_name), rule(rule) {}

    void visit_subobjects(const ManagedVisitor& visitor) override {
      field_name.accept(visitor);
      rule.accept(visitor);
    }
    std::size_t managed_size() const noexcept override {
      return sizeof(record_field_access_t);
    }
  };

  struct tuple_access_t : public Managed {
    std::size_t index;
    managed_ptr<bind_rule_t> rule;

    tuple_access_t(std::size_t index, managed_ptr<bind_rule_t> rule)
        : index(index), rule(rule) {}

    void visit_subobjects(const ManagedVisitor& visitor) override {
      rule.accept(visitor);
    }
    std::size_t managed_size() const noexcept override {
      return sizeof(tuple_access_t);
    }
  };

  std::variant<collections::ArrayPtr<record_field_access_t>,
               collections::ArrayPtr<tuple_access_t>>
      subtype_bindings;

  bool empty() const {
    return !names && visit([](const auto& l) { return !l || l->empty(); },
                           subtype_bindings);
  }

  bool is_tuple() const {
    return subtype_bindings.index() == 1 && !get<1>(subtype_bindings)->empty();
  }

  bool is_record() const {
    return subtype_bindings.index() == 0 && !get<0>(subtype_bindings)->empty();
  }

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (names) names.accept(visitor);
    visit(
        [&](auto& l) {
          if (l) l.accept(visitor);
        },
        subtype_bindings);
  }
  std::size_t managed_size() const noexcept override {
    return sizeof(bind_rule_t);
  }
};

/**
 * A simplified pattern for destructured matching.
 *
 * It is designed to be used in contexts where (a) type checking has
 * already succeeded and (b) bindings are irrelevant, so there are
 * only 4 types of patterns:
 *  - '_': Matches all values of the correct type.
 *  - 'c(p?)': Matches a value with constructor c and argument
 *    matching p.
 *  - '(p1, p2, ..., pn)': Matches a tuple with elements matching
 *    p1, p2, ..., pn.
 *  - '{f1: p1, f2: p2, ..., fn: pn}': Matches a record whose
 *    field f1 matches p1, etc; the pattern need not be
 *    exhaustive over all the record's fields.
 */
struct pattern_t : public Managed {
  static managed_ptr<pattern_t> wildcard();
  static managed_ptr<pattern_t> constructed(
      StringPtr constructor, managed_ptr<typing::TypeName> type_name,
      typing::TypePtr arg_type, collections::ArrayPtr<pattern_t> subpatterns);
  static managed_ptr<pattern_t> tuple(
      collections::ArrayPtr<pattern_t> subpatterns);
  // field must be set on each subpattern; subpatterns must be sorted
  // by field name.
  static managed_ptr<pattern_t> record(
      collections::ArrayPtr<pattern_t> subpatterns);

  bool is_wildcard() const;
  bool is_tuple() const;
  bool is_record() const;
  bool is_record_field() const;
  bool is_constructed() const;

  // is_constructed() must be true.
  StringPtr constructor() const;
  // is_constructed() must be true.
  managed_ptr<typing::TypeName> type_name() const;
  // is_constructed() must be true. May be null.
  typing::TypePtr arg_type() const;
  // is_wildcard() must be false.
  collections::ArrayPtr<pattern_t> subpatterns() const;
  // is_record_field() must be true.
  StringPtr field() const;

  /** Convert this to a record field matcher. */
  void set_field(StringPtr field);

  /**
   * Expand this pattern based on match_type.
   *
   * Expansion rules:
   * - When match_type is an n-tuple:
   *   o if is_wildcard(), expand n wildcard patterns based on the
   *     the subtypes of match_type.
   *   o Otherwise, expand the subpatterns based on the subtypes of
   *     match_type.
   * - When match_type is a record:
   *   o if is_wildcard(), expand a wildcard pattern for each field
   *     in match_type based on each field's type.
   *   o Otherwise, for each field in match_type, if the field is
   *     present in subpatterns, expand it based on the field's type;
   *     if it's not, expand a wildcard pattern based on the field's
   *     type.
   * - When match_type is a constructed type, put pattern into out.
   * - Otherwise, do not modify out.
   */
  friend void expand(managed_ptr<pattern_t> pat,
                     std::vector<managed_ptr<pattern_t>>& out,
                     const typing::Type& match_type);

  /** Apply substitutions to types stored in this pattern. */
  managed_ptr<pattern_t> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(pattern_t);
  }

 private:
  struct wildcard_t {};

  struct constructed_t {
    StringPtr constructor;
    managed_ptr<typing::TypeName> type_name;
    typing::TypePtr arg_type;
    collections::ArrayPtr<pattern_t> subpatterns;
  };

  struct tuple_t {
    collections::ArrayPtr<pattern_t> subpatterns;
  };

  struct record_t {
    collections::ArrayPtr<pattern_t> subpatterns;
  };

  using repr = std::variant<wildcard_t, constructed_t, tuple_t, record_t>;
  repr repr_;
  StringPtr field_;  // Used for matching records

 public:
  pattern_t(repr r);
};

/** A typed pattern. */
class TPattern : public Managed {
 public:
  const Location location;
  const typing::TypePtr type;
  const managed_ptr<pattern_t> pat;
  const managed_ptr<typing::ValEnv> bindings;
  const managed_ptr<bind_rule_t> bind_rule;

  TPattern(const Location& location, typing::TypePtr type,
           managed_ptr<pattern_t> pat, managed_ptr<typing::ValEnv> bindings,
           managed_ptr<bind_rule_t> bind_rule);

  managed_ptr<TPattern> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TPattern);
  }
};

struct dt_leaf_t {
  std::size_t outcome;
};

struct dt_fail_t {};

struct dt_switch_t;

/**
 * A decision tree used to choose which pattern matches a value.
 *
 * Each decision is one of
 * - Failure: This value does not match any pattern.
 * - Leaf(k): This value matches pattern k.
 * - Switch(i, cases): This value's current i'th subpattern is a
 *   constructed type; select the decision tree based on the
 *   constructor used (or "_" if the constructor is not present in the
 *   cases) and continue matching after
 *     1. swapping the i'th subpattern with the last.
 *     2. replacing the last subpattern with the expansion of any
 *        arguments to the constructor (see pattern_t::expand).
 */
using decision_tree_t = std::variant<dt_fail_t, dt_leaf_t, dt_switch_t>;

void visit_subobjects(decision_tree_t& t, const ManagedVisitor& visitor);

struct dt_switch_subtree_t;

struct dt_switch_t {
  static const std::u8string DEFAULT_KEY;
  std::size_t index;
  collections::MapPtr<ManagedString, dt_switch_subtree_t> cases;

  explicit dt_switch_t(std::size_t index);

  ~dt_switch_t();
  dt_switch_t(const dt_switch_t&) noexcept;
  dt_switch_t& operator=(const dt_switch_t&) noexcept;
};

struct dt_switch_subtree_t : public Managed {
  decision_tree_t t;

  dt_switch_subtree_t(decision_tree_t&& t) : t(std::move(t)) {}
  const decision_tree_t& operator*() const { return t; }

  void visit_subobjects(const ManagedVisitor& visitor) override {
    emil::visit_subobjects(t, visitor);
  }
  std::size_t managed_size() const noexcept override {
    return sizeof(dt_switch_subtree_t);
  }
};

class TBigintLiteralExpr;
class TIntLiteralExpr;
class TFpLiteralExpr;
class TStringLiteralExpr;
class TCharLiteralExpr;
class TFstringLiteralExpr;
class TIdentifierExpr;
class TRecRowExpr;
class TRecordExpr;
class TTupleExpr;
class TSequencedExpr;
class TListExpr;
class TLetExpr;
class TApplicationExpr;
class TCaseExpr;
class TFnExpr;

/** A typed expression. */
class TExpr : public Managed {
 public:
  /** The source location the expression starts. */
  const Location location;
  /** The type the expression evaluates to. */
  const typing::TypePtr type;
  /**
   * Whether the expression is non-expansive.
   *
   * When a val binding is elaborated, the type scheme(s) associated
   * with the identifier(s) bound depend on whether the expression
   * used in the binding's assignment is non-expansive. If it is, the
   * scheme(s) generalize over the type variables introduced in the
   * binding and are thus possibly polymorphic. If not, no
   * generalization is performed and the type(s) are monomorphic. See
   * sections 4.7 and 4.8 of the Definition of Standard ML (Revised).
   */
  const bool is_nonexpansive;

  TExpr(const Location& location, typing::TypePtr type, bool is_nonexpansive);
  virtual ~TExpr();

  class Visitor {
   public:
    virtual ~Visitor();

    virtual void visit(const TBigintLiteralExpr& v) = 0;
    virtual void visit(const TIntLiteralExpr& v) = 0;
    virtual void visit(const TFpLiteralExpr& v) = 0;
    virtual void visit(const TStringLiteralExpr& v) = 0;
    virtual void visit(const TCharLiteralExpr& v) = 0;
    virtual void visit(const TFstringLiteralExpr& v) = 0;
    virtual void visit(const TIdentifierExpr& v) = 0;
    virtual void visit(const TRecRowExpr& v) = 0;
    virtual void visit(const TRecordExpr& v) = 0;
    virtual void visit(const TTupleExpr& v) = 0;
    virtual void visit(const TSequencedExpr& v) = 0;
    virtual void visit(const TListExpr& v) = 0;
    virtual void visit(const TLetExpr& v) = 0;
    virtual void visit(const TApplicationExpr& v) = 0;
    virtual void visit(const TCaseExpr& v) = 0;
    virtual void visit(const TFnExpr& v) = 0;
  };

  virtual void accept(Visitor& visitor) const = 0;

  /** Apply substitutions for undetermined types in this expression
   * and all its subexpressions. */
  virtual managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const = 0;

  void visit_subobjects(const ManagedVisitor& visitor) final;
  virtual void visit_texpr_subobjects(const ManagedVisitor& visitor) = 0;
};

/** The elaboration of a pattern match. */
struct match_t : public Managed {
 public:
  struct outcome_t : public Managed {
    managed_ptr<typing::ValEnv> bindings;
    managed_ptr<bind_rule_t> bind_rule;
    managed_ptr<TExpr> result;

    outcome_t(managed_ptr<typing::ValEnv> bindings,
              managed_ptr<bind_rule_t> bind_rule, managed_ptr<TExpr> result)
        : bindings(bindings), bind_rule(bind_rule), result(result) {}

    void visit_subobjects(const ManagedVisitor& visitor) override {
      bindings.accept(visitor);
      bind_rule.accept(visitor);
      result.accept(visitor);
    }

    std::size_t managed_size() const noexcept override {
      return sizeof(outcome_t);
    }
  };

  Location location;
  /**
   * The type of the value to be matched against.
   *
   * It is important that no further unification be applied to this
   * reference to the type. It is used to control the expansion of
   * pattern matching rows and can be thrown off if an undetermined
   * type or type variable that is irrelevant to the match is replaced
   * by a compound type, e.g. to a tuple.
   */
  typing::TypePtr match_type;
  typing::TypePtr result_type;
  collections::ArrayPtr<outcome_t> outcomes;
  decision_tree_t decision_tree;
  bool nonexhaustive;

  /** Applies substitutions to the result_type and outcomes. */
  managed_ptr<match_t> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(match_t); }
};

/** A bigint literal. Nonexpansive. */
class TBigintLiteralExpr : public TExpr {
 public:
  managed_ptr<bigint> value;

  TBigintLiteralExpr(const Location& location, typing::TypePtr type,
                     managed_ptr<bigint> value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TBigintLiteralExpr);
  }
};

/** An int literal. Nonexpansive. */
class TIntLiteralExpr : public TExpr {
 public:
  std::int64_t value;

  TIntLiteralExpr(const Location& location, typing::TypePtr type,
                  std::int64_t value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TIntLiteralExpr);
  }
};

/** A floating point literal. Nonexpansive. */
class TFpLiteralExpr : public TExpr {
 public:
  double value;

  TFpLiteralExpr(const Location& location, typing::TypePtr type, double value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TFpLiteralExpr);
  }
};

/** A string literal. Nonexpansive. */
class TStringLiteralExpr : public TExpr {
 public:
  StringPtr value;

  TStringLiteralExpr(const Location& location, typing::TypePtr type,
                     StringPtr value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TStringLiteralExpr);
  }
};

/** A character literal. Nonexpansive. */
class TCharLiteralExpr : public TExpr {
 public:
  char32_t value;

  TCharLiteralExpr(const Location& location, typing::TypePtr type,
                   char32_t value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TCharLiteralExpr);
  }
};

/** A formatted string literal. Nonexpansive iff all substitutions are
 * nonexpanisive. */
class TFstringLiteralExpr : public TExpr {
 public:
  collections::ArrayPtr<ManagedString> segments;
  collections::ArrayPtr<TExpr> substitutions;

  TFstringLiteralExpr(const Location& location, typing::TypePtr type,
                      collections::ArrayPtr<ManagedString> segments,
                      collections::ArrayPtr<TExpr> substitutions);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TFstringLiteralExpr);
  }
};

/** An identifier expression. Nonexpansive. */
class TIdentifierExpr : public TExpr {
 public:
  typing::IdStatus status;
  collections::ArrayPtr<ManagedString> qualifiers;
  StringPtr canonical_identifier;

  TIdentifierExpr(const Location& location, typing::TypePtr type,
                  typing::IdStatus status,
                  collections::ArrayPtr<ManagedString> qualifiers,
                  StringPtr canonical_identifier);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TIdentifierExpr);
  }
};

/**
 * A record row expression. Nonexpansive iff its value is nonexpansive.
 *
 * This is sort of a quasi-expression type; it's almost never correct
 * for visitors to visit this through `visit`; instead record rows
 * should be processed as part of the enclosing record.
 */
class TRecRowExpr : public TExpr {
 public:
  StringPtr label;
  managed_ptr<TExpr> value;

  TRecRowExpr(const Location& location, typing::TypePtr type, StringPtr label,
              managed_ptr<TExpr> value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TRecRowExpr> apply_substitutions_as_rec_row(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const;
  managed_ptr<TExpr> apply_substitutions(typing::Substitutions,
                                         bool) const override {
    throw std::logic_error("unreachable");
  }

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TRecRowExpr);
  }
};

/** A record expression. Nonexpansive iff all its rows are nonexpansive. */
class TRecordExpr : public TExpr {
 public:
  collections::ArrayPtr<TRecRowExpr> rows;

  TRecordExpr(const Location& location, typing::TypePtr type,
              collections::ArrayPtr<TRecRowExpr> rows);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TRecordExpr);
  }
};

/** A tuple expression. Nonexpansive iff all its elements are nonexpansive. */
class TTupleExpr : public TExpr {
 public:
  collections::ArrayPtr<TExpr> exprs;

  TTupleExpr(const Location& location, typing::TypePtr type,
             collections::ArrayPtr<TExpr> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TTupleExpr);
  }
};

/** A sequenced expression. Expansive. */
class TSequencedExpr : public TExpr {
 public:
  collections::ArrayPtr<TExpr> exprs;

  TSequencedExpr(const Location& location, typing::TypePtr type,
                 collections::ArrayPtr<TExpr> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TSequencedExpr);
  }
};

/** A list expression. Nonexpansive iff all its elements are nonexpansive. */
class TListExpr : public TExpr {
 public:
  collections::ArrayPtr<TExpr> exprs;

  TListExpr(const Location& location, typing::TypePtr type,
            collections::ArrayPtr<TExpr> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TListExpr);
  }
};

/** A let expression. Expansive. */
class TLetExpr : public TExpr {
 public:
  collections::ArrayPtr<TDecl> decls;
  collections::ArrayPtr<TExpr> exprs;

  TLetExpr(const Location& location, typing::TypePtr type,
           collections::ArrayPtr<TDecl> decls,
           collections::ArrayPtr<TExpr> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TLetExpr);
  }
};

/**
 * A function application expression. Expansiveness depends on context.
 *
 * Function applications can be "true" function applications, or else
 * application of a type constructor or exception constructor. True
 * function applications are expansive. Application of a type
 * constructor (except `ref`) or exception constructor to a nonexpansive
 * expression is nonexpansive.
 *
 * This information is available in the elaboration context and should
 * be computed by the elaborator when constructing this object.
 */
class TApplicationExpr : public TExpr {
 public:
  collections::ArrayPtr<TExpr> exprs;

  TApplicationExpr(const Location& location, typing::TypePtr type,
                   bool is_nonexpansive, collections::ArrayPtr<TExpr> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TApplicationExpr);
  }
};

/** A case expression. Expansive. */
class TCaseExpr : public TExpr {
 public:
  managed_ptr<TExpr> expr;
  managed_ptr<match_t> match;

  TCaseExpr(const Location& location, managed_ptr<TExpr> expr,
            managed_ptr<match_t> match);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TCaseExpr);
  }
};

/** A function literal expression. Nonexpansive. */
class TFnExpr : public TExpr {
 public:
  managed_ptr<match_t> match;

  TFnExpr(const Location& location, typing::TypePtr type,
          managed_ptr<match_t> match);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  managed_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void visit_texpr_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override { return sizeof(TFnExpr); }
};

class TValDecl;
class TDtypeDecl;

/** A typed declaration. */
class TDecl : public Managed {
 public:
  const Location location;
  const managed_ptr<typing::Env> env;

  explicit TDecl(const Location& location, managed_ptr<typing::Env> env);
  virtual ~TDecl();

  class Visitor {
   public:
    virtual ~Visitor();

    virtual void visit(const TValDecl& node) = 0;
    virtual void visit(const TDtypeDecl& node) = 0;
  };

  virtual void accept(Visitor& visitor) const = 0;
  virtual managed_ptr<TDecl> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const = 0;

  void visit_subobjects(const ManagedVisitor& visitor) final;
  virtual void visit_tdecl_subobjects(const ManagedVisitor& visitor) = 0;
};

class TValBind : public Managed {
 public:
  managed_ptr<match_t> match;
  managed_ptr<TExpr> expr;

  explicit TValBind(managed_ptr<match_t> match);
  TValBind(managed_ptr<match_t> match, managed_ptr<TExpr> expr);

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TValBind);
  }
};

class TValDecl : public TDecl {
 public:
  const collections::ArrayPtr<TValBind> bindings;

  TValDecl(const Location& location, collections::ArrayPtr<TValBind> bindings,
           managed_ptr<typing::Env> env);

  managed_ptr<TDecl> apply_substitutions(
      typing::Substitutions substitutions,
      bool enforce_timing_constraints) const override;

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  void visit_tdecl_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TValDecl);
  }
};

class TDtypeDecl : public TDecl {
 public:
  TDtypeDecl(const Location& location, managed_ptr<typing::Env> env);

  managed_ptr<TDecl> apply_substitutions(typing::Substitutions,
                                         bool) const override {
    return make_managed<TDtypeDecl>(location, env);
  }

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  void visit_tdecl_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TDtypeDecl);
  }
};

class TEmptyTopDecl;
class TEndOfFileTopDecl;
class TDeclTopDecl;

/** A typed top-level declaration. */
class TTopDecl : public Managed {
 public:
  const Location location;

  explicit TTopDecl(const Location& location);
  virtual ~TTopDecl();

  class Visitor {
   public:
    virtual ~Visitor();

    virtual void visit(const TEmptyTopDecl& v) = 0;
    virtual void visit(const TEndOfFileTopDecl& v) = 0;
    virtual void visit(const TDeclTopDecl& v) = 0;
  };

  virtual void accept(Visitor& visitor) const = 0;
};

class TEmptyTopDecl : public TTopDecl {
 public:
  using TTopDecl::TTopDecl;

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TEmptyTopDecl);
  }
};

class TEndOfFileTopDecl : public TTopDecl {
 public:
  using TTopDecl::TTopDecl;

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(TEndOfFileTopDecl);
  }
};

class TDeclTopDecl : public TTopDecl {
 public:
  managed_ptr<TDecl> decl;

  TDeclTopDecl(const Location& location, managed_ptr<TDecl> decl);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TDeclTopDecl);
  }
};

}  // namespace emil
