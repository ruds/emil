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

#include "emil/token.h"
#include "emil/types.h"

namespace emil {

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

/** A typed expression. */
class TExpr {
 public:
  const Location location;

  explicit TExpr(const Location& location);
  virtual ~TExpr();

  class Visitor {
   public:
    virtual ~Visitor();
  };

  virtual typing::TypePtr type() const = 0;
  virtual void accept(Visitor& visitor) const = 0;
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
