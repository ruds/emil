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

#include <emil/collections.h>

#include <cstdint>
#include <exception>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "emil/ast.h"  // IWYU pragma: keep
#include "emil/gc.h"
#include "emil/token.h"
#include "emil/typed_ast.h"  // IWYU pragma: keep
#include "emil/types.h"

namespace emil {

class Reporter;

/** Error thrown due to error in static elaboration. */
class ElaborationError : public std::exception {
 public:
  ElaborationError(std::string msg, const Location& location);
  ElaborationError(const typing::UnificationError& err,
                   const Location& location);

  virtual const char* what() const noexcept override {
    return full_msg.c_str();
  }

  const std::string msg;
  const Location location;
  const std::string full_msg;
};

std::string describe_basis_updates(const TTopDecl& topdecl);

/**
 * Performs static elaboration of a program.
 *
 * The primary operation of static elaboration is deducing types and
 * checking related constraints.
 */
class Typer {
 public:
  explicit Typer(Reporter& reporter);

  managed_ptr<typing::Basis> initial_basis() const;

  struct elaborate_topdecl_t {
    managed_ptr<typing::Basis> B;
    std::unique_ptr<TTopDecl> topdecl;
  };

  /** Do typing analysis of a top-level declaration. */
  elaborate_topdecl_t elaborate(managed_ptr<typing::Basis> B,
                                const TopDecl& topdecl);

  struct elaborate_decl_t {
    managed_ptr<typing::Env> env;
    std::unique_ptr<TDecl> decl;
  };

  /** Do typing analysis of a declaration. */
  elaborate_decl_t elaborate(managed_ptr<typing::Context> C, const Decl& dec);

  struct elaborate_decl_with_substitutions_t {
    managed_ptr<typing::Env> env;
    std::unique_ptr<TDecl> decl;
    typing::Substitutions new_substitutions;
  };

  /** Do typing analysis of a declaration. */
  elaborate_decl_with_substitutions_t elaborate(
      managed_ptr<typing::Context> C, const Decl& dec,
      typing::Substitutions& substitutions);

  /** Do typing analysis of an expression. */
  std::unique_ptr<TExpr> elaborate(managed_ptr<typing::Context> C,
                                   const Expr& exp);

  struct elaborate_expr_with_substitutions_t {
    std::unique_ptr<TExpr> expr;
    typing::Substitutions new_substitutions;
  };

  /**
   * Do typing analysis of an expression.
   *
   * The given substitutions are applied to the expression's subtypes;
   * newly deduced substitutions are added to substitutions as well as
   * being returned separately in the result's new_substitutions
   * field.
   */
  elaborate_expr_with_substitutions_t elaborate(
      managed_ptr<typing::Context> C, const Expr& exp,
      typing::Substitutions& substitutions, std::uint64_t maximum_type_name_id);

  struct elaborate_match_t {
    match_t match;
    typing::Substitutions new_substitutions =
        collections::managed_map<typing::Stamp, typing::Type>({});
  };

  elaborate_match_t elaborate_match(
      const Location& location, managed_ptr<typing::Context> C,
      const std::vector<
          std::pair<std::unique_ptr<Pattern>, std::unique_ptr<Expr>>>& cases,
      typing::Substitutions& substitutions, std::uint64_t maximum_type_name_id);

  elaborate_match_t elaborate_match(const Location& location,
                                    managed_ptr<typing::Context> C,
                                    const Pattern& pat,
                                    typing::Substitutions& substitutions,
                                    std::uint64_t maximum_type_name_id);

  managed_ptr<typing::Type> elaborate_type_expr(managed_ptr<typing::Context> C,
                                                const TypeExpr& ty);

  std::unique_ptr<TPattern> elaborate_pattern(managed_ptr<typing::Context> C,
                                              const Pattern& pat);

  managed_ptr<typing::Stamp> new_stamp();
  typing::StampGenerator& stamper() { return stamp_generator_; }
  const typing::BuiltinTypes& builtins() const;

  void issue_warning(const Location& location, std::string_view text);

 private:
  typing::StampGenerator stamp_generator_;
  typing::BuiltinTypes builtins_;
  Reporter& reporter_;
};

}  // namespace emil
