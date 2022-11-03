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

#include "emil/gc.h"

namespace emil {

class TopDecl;
class TTopDecl;

namespace typing {
class Basis;
}

class Typer {
 public:
  /** Do typing analysis of a top-level declaration. */
  std::pair<std::unique_ptr<TTopDecl>, managed_ptr<typing::Basis>> elaborate(
      managed_ptr<typing::Basis> B, const TopDecl& topdec);
};
}  // namespace emil
