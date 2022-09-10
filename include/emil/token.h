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

#include <gmpxx.h>

#include <algorithm>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <variant>

#include "enum.h"
#include "utf8.h"

namespace emil {

#define TOKEN_TYPE_LIST(DECLARE, X) \
  DECLARE(END, X)                   \
  DECLARE(ILITERAL, X)              \
  DECLARE(FPLITERAL, X)             \
  DECLARE(CHAR, X)                  \
  DECLARE(STRING, X)                \
  DECLARE(FSTRING, X)               \
  DECLARE(FSTRING_CONT, X)          \
  DECLARE(FSTRING_IVAR, X)          \
  DECLARE(FSTRING_IEXPR_S, X)       \
  DECLARE(FSTRING_IEXPR_F, X)       \
  DECLARE(ID_WORD, X)               \
  DECLARE(ID_OP, X)

ENUM_WITH_TEXT(TokenType, TOKEN_TYPE_LIST)

using token_auxiliary_t = std::variant<std::monostate, int64_t, mpz_class,
                                       double, char32_t, std::u8string>;

struct Token {
  const std::u32string text;
  const int line;
  const TokenType type;
  const token_auxiliary_t aux;
};

}  // namespace emil

ENUM_WITH_TEXT_FORMATTER(emil::TokenType)

template <>
struct fmt::formatter<emil::Token> {
  template <typename... Ts>
  struct overload : Ts... {
    using Ts::operator()...;
  };
  template <typename... Ts>
  overload(Ts...) -> overload<Ts...>;

  // cppcheck-suppress functionStatic
  constexpr auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end && *it != '}') throw format_error("invalid format");
    return it;
  }

  template <typename FormatContext>
  auto format(const emil::Token& t, FormatContext& ctx) const
      -> decltype(ctx.out()) {
    using emil::TokenType;
    using fmt::format;

    std::string aux;
    switch (t.type) {
      case TokenType::END:
        aux = "";
        break;

      case TokenType::ILITERAL: {
        aux = visit(
            overload{[](int64_t i) { return format("{}i", i); },
                     [](const mpz_class& n) { return n.get_str(); },
                     [](const auto&) -> std::string {
                       throw std::logic_error("Bad aux type for ILITERAL");
                     }},
            t.aux);
        break;
      }

      case TokenType::FPLITERAL:
        aux = format("{:.13e}", get<double>(t.aux));
        break;

      case TokenType::CHAR:
        aux = format("{:06X}", (std::uint32_t)get<char32_t>(t.aux));
        break;

      case TokenType::STRING:
      case TokenType::ID_WORD:
      case TokenType::ID_OP: {
        auto it = back_inserter(aux);
        for (char8_t c : get<std::u8string>(t.aux)) {
          fmt::format_to(it, "{:02X}", (unsigned int)c);
        }
        break;
      }

      default:
        throw std::logic_error("Unhandled token type.");
    }
    return fmt::format_to(ctx.out(), "{:04} {}{}{}{}{}", t.line, t.type,
                          aux.empty() ? "" : " ", aux,
                          t.text.empty() ? "" : " ", utf8::utf32to8(t.text));
  }
};
