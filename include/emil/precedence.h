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

#include <unordered_map>

namespace emil {

enum class fixity {
  LEFT,
  RIGHT,
  NONE,
  PREFIX,
};

struct precedence_t {
  int level;
  fixity fixity;
};

constexpr int MIN_PRECEDENCE = 0;
constexpr int MAX_PRECEDENCE = 9;

constexpr precedence_t DEFAULT_INFIX_PRECEDENCE{.level = MIN_PRECEDENCE,
                                                .fixity = fixity::LEFT};

constexpr precedence_t DEFAULT_PREFIX_PRECEDENCE{.level = MAX_PRECEDENCE,
                                                 .fixity = fixity::PREFIX};

struct precedence_table {
  std::unordered_map<std::u8string, precedence_t> infix_precedence;
  std::unordered_map<std::u8string, precedence_t> prefix_precedence;
};

}  // namespace emil
