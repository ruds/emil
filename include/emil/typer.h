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

#include "emil/ast.h"  // IWYU pragma: keep
#include "emil/gc.h"
#include "emil/typed_ast.h"  // IWYU pragma: keep
#include "emil/types.h"      // IWYU pragma: keep

namespace emil {

class Typer {
 public:
  struct UnificationResult {
    std::unique_ptr<typing::Type> unified_type;
  };

  Typer();

  /** Do typing analysis of a top-level declaration. */
  std::pair<managed_ptr<typing::Basis>, std::unique_ptr<TTopDecl>> elaborate(
      managed_ptr<typing::Basis> B, const TopDecl& topdec);

  /** Do typing analysis of a declaration. */
  std::pair<managed_ptr<typing::Env>, std::unique_ptr<TDecl>> elaborate(
      managed_ptr<typing::Context> C, const Decl& dec);

  /** Do typing analysis of an expression. */
  std::unique_ptr<TExpr> elaborate(managed_ptr<typing::Context> C,
                                   const Expr& exp);

  /** Unify two types. */
  UnificationResult unify(managed_ptr<typing::Type> l,
                          managed_ptr<typing::Type> r);

  managed_ptr<typing::Stamp> new_stamp();
  const typing::BuiltinTypes& builtins() const;

 private:
  typing::StampGenerator stamp_generator_;
  typing::BuiltinTypes builtins_;
};

}  // namespace emil
