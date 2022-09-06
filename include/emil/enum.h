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

#include <fmt/format.h>

/** Declares an enum and functions that convert enum values to text.
 *
 * # Usage
 * Define a macro that takes two arguments, `DECLARE` and `X`,
 * and expands into zero or more declarations `DECLARE(ENUM1, X)`.
 * Then pass the desired name of the enum along with the list to
 * the `ENUM_WITH_TEXT` macro.
 *
 * # Example
 * The following code:
 *
 *     #define METAVAR_LIST(DECLARE, X) \
 *         DECLARE(foo, X) \
 *         DECLARE(bar, X) \
 *         DECLARE(baz, X)
 *     ENUM_WITH_TEXT(Metavar, METAVAR_LIST)
 *
 * will expand into an `enum class` named `Metavar` with values
 * `foo`, `bar`, and `baz`, along with a template function
 * with signature
 *
 *    template <Metavar VAL> constexpr const char* MetavarText()
 *
 * and another function with signature
 *
 *    constexpr const char* MetavarText(Metavar val);
 *
 * These functions return a pointer to a `const char*` with the same
 * value as the enumerator name.
 */
#define ENUM_WITH_TEXT(Name, LIST)                        \
  enum class Name { LIST(ENUM_WITH_TEXT_ENTRY, unused) }; \
  template <Name VAL>                                     \
  constexpr const char* Name##Text() = delete;            \
  LIST(ENUM_WITH_TEXT_FUNC, Name)                         \
  constexpr const char* Name##Text(Name val) {            \
    switch (val) { LIST(ENUM_WITH_TEXT_CASE, Name) }      \
    return nullptr;                                       \
  }

/**
 * Defines a specialization of fmt::formatter for the given enum.
 *
 * Must be used outside of any namespace.
 */
#define ENUM_WITH_TEXT_FORMATTER(Name)                             \
  template <>                                                      \
  struct fmt::formatter<Name> : formatter<std::string> {           \
    template <typename FormatContext>                              \
    auto format(Name val, FormatContext& ctx) const {              \
      return formatter<std::string>::format(Name##Text(val), ctx); \
    }                                                              \
  };

#define ENUM_WITH_TEXT_ENTRY(N, X) N,

#define ENUM_WITH_TEXT_FUNC(N, X)         \
  template <>                             \
  constexpr const char* X##Text<X::N>() { \
    return #N;                            \
  }

#define ENUM_WITH_TEXT_CASE(N, X) \
  case X::N:                      \
    return X##Text<X::N>();
