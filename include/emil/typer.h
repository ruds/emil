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
#include <utility>

#include "emil/ast.h"
#include "emil/gc.h"
#include "emil/typed_ast.h"
#include "emil/types.h"  // IWYU pragma: keep

namespace emil {

class Typer {
 public:
  /** Do typing analysis of a top-level declaration. */
  std::pair<managed_ptr<typing::Basis>, std::unique_ptr<TTopDecl>> elaborate(
      managed_ptr<typing::Basis> B, const TopDecl& topdec);

  /** Do typing analysis of a declaration. */
  std::pair<managed_ptr<typing::Env>, std::unique_ptr<TDecl>> elaborate(
      managed_ptr<typing::Context> C, const Decl& dec);

  /** Do typing analysis of an expression. */
  std::unique_ptr<TExpr> elaborate(managed_ptr<typing::Context> C,
                                   const Expr& exp);

 private:
  class TopDeclElaborator : public TopDecl::Visitor {
   public:
    managed_ptr<typing::Basis> B;
    std::unique_ptr<TTopDecl> typed;

    TopDeclElaborator(Typer& typer, managed_ptr<typing::Basis> B);

    DECLARE_TOPDECL_V_FUNCS;

   private:
    Typer& typer_;
  };
};

}  // namespace emil
