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

#include "emil/typer.h"

#include "emil/ast.h"
#include "emil/typed_ast.h"
#include "emil/types.h"

namespace emil {

std::pair<managed_ptr<typing::Basis>, std::unique_ptr<TTopDecl>>
Typer::elaborate(managed_ptr<typing::Basis> B, const TopDecl &topdec) {
  TopDeclElaborator v(*this, std::move(B));
  topdec.accept(v);
  return std::make_pair(std::move(v.B), std::move(v.typed));
}

Typer::TopDeclElaborator::TopDeclElaborator(Typer &typer,
                                            managed_ptr<typing::Basis> B)
    : B(std::move(B)), typer_(typer) {}

void Typer::TopDeclElaborator::visitEmptyTopDecl(const EmptyTopDecl &node) {
  typed = std::make_unique<TEmptyTopDecl>(node.location);
}

void Typer::TopDeclElaborator::visitEndOfFileTopDecl(
    const EndOfFileTopDecl &node) {
  typed = std::make_unique<TEndOfFileTopDecl>(node.location);
}

void Typer::TopDeclElaborator::visitExprTopDecl(const ExprTopDecl &node) {
  typed = std::make_unique<TExprTopDecl>(
      node.location, typer_.elaborate(B->as_context(), *node.expr));
}

void Typer::TopDeclElaborator::visitDeclTopDecl(const DeclTopDecl &node) {
  auto r = typer_.elaborate(B->as_context(), *node.decl);
  B = B + r.first;
  typed = std::make_unique<TDeclTopDecl>(node.location, std::move(r.second));
}

}  // namespace emil
