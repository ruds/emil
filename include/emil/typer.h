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

#include <exception>
#include <memory>
#include <string>

#include "emil/ast.h"  // IWYU pragma: keep
#include "emil/gc.h"
#include "emil/token.h"
#include "emil/typed_ast.h"  // IWYU pragma: keep
#include "emil/types.h"      // IWYU pragma: keep

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

class TyperImpl;

/**
 * Performs static elaboration of a program.
 *
 * The primary operation of static elaboration is deducing types and
 * checking related constraints.
 */
class Typer {
 public:
  explicit Typer(Reporter& reporter);
  ~Typer();

  /**
   * Generate an initial static basis for elaboration.
   *
   * Contains the following types:
   * - `bigint`, `int`, `byte`, `float`, `char`, `string`.
   * - `bool` and its value constructors `true` and `false`.
   * - `'a list` and its value constructors `nil` and `::`.
   * - `'a ref` and its value constructor `ref`.
   */
  managed_ptr<typing::Basis> initial_basis() const;

  struct elaborate_t {
    managed_ptr<typing::Basis> B;
    managed_ptr<TTopDecl> topdecl;
  };

  /** Do typing analysis of a top-level declaration. */
  elaborate_t elaborate(managed_ptr<typing::Basis> B, const TopDecl& topdecl);

  /** Produce a string describing changes to `B` due to a top-level declaration.
   */
  std::string describe_basis_updates(const TTopDecl& topdecl);

 private:
  std::unique_ptr<TyperImpl> impl_;
};

}  // namespace emil
