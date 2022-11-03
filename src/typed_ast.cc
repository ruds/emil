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

#include "emil/typed_ast.h"

namespace emil {

TPattern::~TPattern() = default;
TPattern::Visitor::~Visitor() = default;

TExpr::~TExpr() = default;
TExpr::Visitor::~Visitor() = default;

TDecl::~TDecl() = default;
TDecl::Visitor::~Visitor() = default;

TTopDecl::~TTopDecl() = default;
TTopDecl::Visitor::~Visitor() = default;

}  // namespace emil
