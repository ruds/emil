// Copyright 2023 Matt Rudary

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

#include <string>
#include <string_view>

#include "emil/gc.h"
#include "emil/types.h"

namespace emil {

class ExceptionPack;
class TTopDecl;
union value_t;

class Evaluator {
 public:
  virtual ~Evaluator();

  virtual managed_ptr<ExceptionPack> evaluate(const TTopDecl& topdecl) = 0;
  virtual std::string print(typing::TypePtr type, const value_t& value) = 0;
  virtual std::string print(typing::TypePtr type, std::u8string_view name) = 0;
  virtual void visit_root(const ManagedVisitor& visitor) = 0;
};

}  // namespace emil
