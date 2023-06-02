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

#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

#include "emil/bigint.h"  // IWYU pragma: keep
#include "emil/cons.h"
#include "emil/gc.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/types.h"

namespace emil {

class TDecl;

/** A typed pattern. */
class TPattern {
 public:
  const Location location;

  explicit TPattern(const Location& location);
  virtual ~TPattern();

  class Visitor {
   public:
    virtual ~Visitor();
  };

  virtual void accept(Visitor& visitor) const = 0;
  virtual std::unique_ptr<TPattern> apply_substitutions(
      typing::Substitutions substitutions) const = 0;
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
class TExpr {
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
  virtual std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const = 0;
};

/** A bigint literal. Nonexpansive. */
class TBigintLiteralExpr : public TExpr {
 public:
  managed_ptr<bigint> value;

  TBigintLiteralExpr(const Location& location, typing::TypePtr type,
                     managed_ptr<bigint> value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** An int literal. Nonexpansive. */
class TIntLiteralExpr : public TExpr {
 public:
  std::int64_t value;

  TIntLiteralExpr(const Location& location, typing::TypePtr type,
                  std::int64_t value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A floating point literal. Nonexpansive. */
class TFpLiteralExpr : public TExpr {
 public:
  double value;

  TFpLiteralExpr(const Location& location, typing::TypePtr type, double value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A string literal. Nonexpansive. */
class TStringLiteralExpr : public TExpr {
 public:
  StringPtr value;

  TStringLiteralExpr(const Location& location, typing::TypePtr type,
                     StringPtr value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A character literal. Nonexpansive. */
class TCharLiteralExpr : public TExpr {
 public:
  char32_t value;

  TCharLiteralExpr(const Location& location, typing::TypePtr type,
                   char32_t value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A formatted string literal. Nonexpansive iff all substitutions are
 * nonexpanisive. */
class TFstringLiteralExpr : public TExpr {
 public:
  collections::ConsPtr<ManagedString> segments;
  std::vector<std::unique_ptr<TExpr>> substitutions;

  TFstringLiteralExpr(const Location& location, typing::TypePtr type,
                      collections::ConsPtr<ManagedString> segments,
                      std::vector<std::unique_ptr<TExpr>> substitutions);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** An identifier expression. Nonexpansive. */
class TIdentifierExpr : public TExpr {
 public:
  typing::IdStatus status;
  collections::ConsPtr<ManagedString> qualifiers;
  StringPtr canonical_identifier;

  TIdentifierExpr(const Location& location, typing::TypePtr type,
                  typing::IdStatus status,
                  collections::ConsPtr<ManagedString> qualifiers,
                  StringPtr canonical_identifier);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
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
  std::unique_ptr<TExpr> value;

  TRecRowExpr(const Location& location, typing::TypePtr type, StringPtr label,
              std::unique_ptr<TExpr> value);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TRecRowExpr> apply_substitutions_as_rec_row(
      typing::Substitutions substitutions) const;
  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions) const override {
    throw std::logic_error("unreachable");
  }
};

/** A record expression. Nonexpansive iff all its rows are nonexpansive. */
class TRecordExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TRecRowExpr>> rows;

  TRecordExpr(const Location& location, typing::TypePtr type,
              std::vector<std::unique_ptr<TRecRowExpr>> rows);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A tuple expression. Nonexpansive iff all its elements are nonexpansive. */
class TTupleExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TTupleExpr(const Location& location, typing::TypePtr type,
             std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A sequenced expression. Expansive. */
class TSequencedExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TSequencedExpr(const Location& location, typing::TypePtr type,
                 std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A list expression. Nonexpansive iff all its elements are nonexpansive. */
class TListExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TListExpr(const Location& location, typing::TypePtr type,
            std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A let expression. Expansive. */
class TLetExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TDecl>> decls;
  std::vector<std::unique_ptr<TExpr>> exprs;

  TLetExpr(const Location& location, typing::TypePtr type,
           std::vector<std::unique_ptr<TDecl>> decls,
           std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
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
  std::vector<std::unique_ptr<TExpr>> exprs;

  TApplicationExpr(const Location& location, typing::TypePtr type,
                   bool is_nonexpansive,
                   std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A case expression. Expansive. */
class TCaseExpr : public TExpr {
 public:
  std::unique_ptr<TExpr> expr;
  std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
      cases;

  TCaseExpr(
      const Location& location, typing::TypePtr type,
      std::unique_ptr<TExpr> expr,
      std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
          cases);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A function literal expression. Nonexpansive. */
class TFnExpr : public TExpr {
 public:
  std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
      cases;

  TFnExpr(
      const Location& location, typing::TypePtr type,
      std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
          cases);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }

  std::unique_ptr<TExpr> apply_substitutions(
      typing::Substitutions substitutions) const override;
};

/** A typed declaration. */
class TDecl {
 public:
  const Location location;

  explicit TDecl(const Location& location);
  virtual ~TDecl();

  class Visitor {
   public:
    virtual ~Visitor();
  };

  virtual void accept(Visitor& visitor) const = 0;
  virtual std::unique_ptr<TDecl> apply_substitutions(
      typing::Substitutions substitutions) const = 0;
};

class TEmptyTopDecl;
class TEndOfFileTopDecl;
class TExprTopDecl;
class TDeclTopDecl;

/** A typed top-level declaration. */
class TTopDecl {
 public:
  const Location location;

  explicit TTopDecl(const Location& location);
  virtual ~TTopDecl();

  class Visitor {
   public:
    virtual ~Visitor();

    virtual void visit(const TEmptyTopDecl& v) = 0;
    virtual void visit(const TEndOfFileTopDecl& v) = 0;
    virtual void visit(const TExprTopDecl& v) = 0;
    virtual void visit(const TDeclTopDecl& v) = 0;
  };

  virtual void accept(Visitor& visitor) const = 0;
};

class TEmptyTopDecl : public TTopDecl {
 public:
  explicit TEmptyTopDecl(const Location& location);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
};

class TEndOfFileTopDecl : public TTopDecl {
 public:
  explicit TEndOfFileTopDecl(const Location& location);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
};

class TExprTopDecl : public TTopDecl {
 public:
  std::unique_ptr<TExpr> expr;

  TExprTopDecl(const Location& location, std::unique_ptr<TExpr> expr);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
};

class TDeclTopDecl : public TTopDecl {
 public:
  std::unique_ptr<TDecl> decl;

  TDeclTopDecl(const Location& location, std::unique_ptr<TDecl> decl);

  void accept(Visitor& visitor) const override { visitor.visit(*this); }
};

}  // namespace emil
