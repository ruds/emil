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

#include <memory>

#include "emil/bigint.h"  // IWYU pragma: keep
#include "emil/gc.h"
#include "emil/token.h"
#include "emil/types.h"

namespace emil {

class TDecl;
class TExpr;

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
  const Location location;
  const typing::TypePtr type;
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
  };

  virtual void accept(Visitor& visitor) const = 0;
};

class TBigintLiteralExpr : public TExpr {
 public:
  managed_ptr<bigint> value;

  TBigintLiteralExpr(const Location& location, typing::TypePtr type,
                     managed_ptr<bigint> value);

  void accept(Visitor& visitor) const override;
};

class TIntLiteralExpr : public TExpr {
 public:
  int64_t value;

  TIntLiteralExpr(const Location& location, typing::TypePtr type,
                  int64_t value);

  void accept(Visitor& visitor) const override;
};

class TFpLiteralExpr : public TExpr {
 public:
  double value;

  TFpLiteralExpr(const Location& location, typing::TypePtr type, double value);

  void accept(Visitor& visitor) const override;
};

class TStringLiteralExpr : public TExpr {
 public:
  StringPtr value;

  TStringLiteralExpr(const Location& location, typing::TypePtr type,
                     StringPtr value);

  void accept(Visitor& visitor) const override;
};

class TCharLiteralExpr : public TExpr {
 public:
  char32_t value;

  TCharLiteralExpr(const Location& location, typing::TypePtr type,
                   char32_t value);

  void accept(Visitor& visitor) const override;
};

class TFstringLiteralExpr : public TExpr {
 public:
  collections::ConsPtr<ManagedString> segments;
  std::vector<std::unique_ptr<TExpr>> substitutions;

  TFstringLiteralExpr(const Location& location, typing::TypePtr type,
                      collections::ConsPtr<ManagedString> segments,
                      std::vector<std::unique_ptr<TExpr>> substitutions);

  void accept(Visitor& visitor) const override;
};

class TIdentifierExpr : public TExpr {
 public:
  collections::ConsPtr<ManagedString> qualifiers;
  StringPtr identifier;
  bool is_op;
  bool is_prefix_op;

  TIdentifierExpr(const Location& location, typing::TypePtr type,
                  collections::ConsPtr<ManagedString> qualifiers,
                  StringPtr identifier, bool is_op, bool is_prefix_op);

  void accept(Visitor& visitor) const override;
};

class TRecRowExpr : public TExpr {
 public:
  StringPtr label;
  std::unique_ptr<TExpr> value;

  TRecRowExpr(const Location& location, typing::TypePtr type, StringPtr label,
              std::unique_ptr<TExpr> value);

  void accept(Visitor& visitor) const override;
};

class TRecordExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TRecRowExpr>> exprs;

  TRecordExpr(const Location& location, typing::TypePtr type,
              std::vector<std::unique_ptr<TRecRowExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

class TTupleExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TTupleExpr(const Location& location, typing::TypePtr type,
             std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

class TSequencedExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TSequencedExpr(const Location& location, typing::TypePtr type,
                 std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

class TListExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TListExpr(const Location& location, typing::TypePtr type,
            std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

class TLetExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TDecl>> decls;
  std::vector<std::unique_ptr<TExpr>> exprs;

  TLetExpr(const Location& location, typing::TypePtr type,
           std::vector<std::unique_ptr<TDecl>> decls,
           std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

class TApplicationExpr : public TExpr {
 public:
  std::vector<std::unique_ptr<TExpr>> exprs;

  TApplicationExpr(const Location& location, typing::TypePtr type,
                   std::vector<std::unique_ptr<TExpr>> exprs);

  void accept(Visitor& visitor) const override;
};

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

  void accept(Visitor& visitor) const override;
};

class TFnExpr : public TExpr {
 public:
  std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
      cases;

  TFnExpr(
      const Location& location, typing::TypePtr type,
      std::vector<std::pair<std::unique_ptr<TPattern>, std::unique_ptr<TExpr>>>
          cases);

  void accept(Visitor& visitor) const override;
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

  void accept(Visitor& visitor) const override;
};

class TEndOfFileTopDecl : public TTopDecl {
 public:
  explicit TEndOfFileTopDecl(const Location& location);

  void accept(Visitor& visitor) const override;
};

class TExprTopDecl : public TTopDecl {
 public:
  std::unique_ptr<TExpr> expr;

  TExprTopDecl(const Location& location, std::unique_ptr<TExpr> expr);

  void accept(Visitor& visitor) const override;
};

class TDeclTopDecl : public TTopDecl {
 public:
  std::unique_ptr<TDecl> decl;

  TDeclTopDecl(const Location& location, std::unique_ptr<TDecl> decl);

  void accept(Visitor& visitor) const override;
};

}  // namespace emil
