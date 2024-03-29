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

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "emil/enum.h"
#include "emil/misc.h"
#include "emil/strconvert.h"

namespace emil {

#define TOKEN_TYPE_LIST(DECLARE, X) \
  DECLARE(END_OF_FILE, X)           \
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
  DECLARE(ID_TYPE, X)               \
  DECLARE(ID_OP, X)                 \
  DECLARE(QUAL_ID_WORD, X)          \
  DECLARE(QUAL_ID_OP, X)            \
  DECLARE(KW_AND, X)                \
  DECLARE(KW_AS, X)                 \
  DECLARE(KW_CASE, X)               \
  DECLARE(KW_DATATYPE, X)           \
  DECLARE(KW_ELSE, X)               \
  DECLARE(KW_END, X)                \
  DECLARE(KW_EXCEPTION, X)          \
  DECLARE(KW_FN, X)                 \
  DECLARE(KW_FUN, X)                \
  DECLARE(KW_HANDLE, X)             \
  DECLARE(KW_IF, X)                 \
  DECLARE(KW_IMPLICIT, X)           \
  DECLARE(KW_IN, X)                 \
  DECLARE(KW_INFIX, X)              \
  DECLARE(KW_INFIXR, X)             \
  DECLARE(KW_LET, X)                \
  DECLARE(KW_LOCAL, X)              \
  DECLARE(KW_NONFIX, X)             \
  DECLARE(KW_OF, X)                 \
  DECLARE(KW_OPEN, X)               \
  DECLARE(KW_PREFIX, X)             \
  DECLARE(KW_RAISE, X)              \
  DECLARE(KW_REC, X)                \
  DECLARE(KW_THEN, X)               \
  DECLARE(KW_TYPE, X)               \
  DECLARE(KW_UNDERSCORE, X)         \
  DECLARE(KW_VAL, X)                \
  DECLARE(KW_WHILE, X)              \
  DECLARE(KW_WITHTYPE, X)           \
  DECLARE(COLON, X)                 \
  DECLARE(PIPE, X)                  \
  DECLARE(TO_EXPR, X)               \
  DECLARE(TO_TYPE, X)               \
  DECLARE(HASH, X)                  \
  DECLARE(LPAREN, X)                \
  DECLARE(RPAREN, X)                \
  DECLARE(LBRACKET, X)              \
  DECLARE(RBRACKET, X)              \
  DECLARE(LBRACE, X)                \
  DECLARE(RBRACE, X)                \
  DECLARE(COMMA, X)                 \
  DECLARE(SEMICOLON, X)             \
  DECLARE(EQUALS, X)                \
  DECLARE(ASTERISK, X)              \
  DECLARE(ELLIPSIS, X)

ENUM_WITH_TEXT(TokenType, TOKEN_TYPE_LIST)

struct QualifiedIdentifier {
  std::vector<std::u8string> qualifiers;
  std::u8string id;

  std::string to_string() const {
    std::ostringstream out;
    std::transform(qualifiers.begin(), qualifiers.end(),
                   std::ostream_iterator<std::string>(out, "."),
                   [](std::u8string_view s) { return to_hex(s); });
    out << to_hex(id);
    return out.str();
  }
};

struct BigintLiteralData {
  std::u8string number;
  int base;
};

using token_auxiliary_t =
    std::variant<std::monostate, int64_t, BigintLiteralData, double, char32_t,
                 std::u8string, QualifiedIdentifier>;

struct Location {
  std::string_view filename;
  int line;
};

struct Token {
  std::u32string text;
  Location location;
  TokenType type;
  token_auxiliary_t aux;
};

}  // namespace emil

ENUM_WITH_TEXT_FORMATTER(emil::TokenType)

template <>
struct fmt::formatter<emil::BigintLiteralData> {
  // cppcheck-suppress functionStatic
  constexpr auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end) throw format_error("invalid format");
    return it;
  }

  template <typename FormatContext>
  // cppcheck-suppress functionStatic
  auto format(const emil::BigintLiteralData& d, FormatContext& ctx) const
      -> decltype(ctx.out()) {
    std::string base;
    switch (d.base) {
      case 2:
        base = "0b";
        break;
      case 8:
        base = "0o";
        break;
      case 16:
        base = "0x";
        break;
    }
    return fmt::format_to(ctx.out(), "{}{}", base,
                          emil::to_std_string(d.number));
  }
};

template <>
struct fmt::formatter<emil::Token> {
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
      case TokenType::ILITERAL: {
        aux = visit(emil::overloaded{[](int64_t i) { return format("{}i", i); },
                                     [](const emil::BigintLiteralData& d) {
                                       return fmt::format("{}", d);
                                     },
                                     [](const auto&) -> std::string {
                                       throw std::logic_error(
                                           "Bad aux type for ILITERAL");
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
      case TokenType::FSTRING:
      case TokenType::FSTRING_CONT:
      case TokenType::FSTRING_IVAR:
      case TokenType::ID_WORD:
      case TokenType::ID_TYPE:
      case TokenType::ID_OP:
        emil::to_hex(get<std::u8string>(t.aux), aux);
        break;

      case TokenType::QUAL_ID_WORD:
      case TokenType::QUAL_ID_OP:
        aux = get<emil::QualifiedIdentifier>(t.aux).to_string();
        break;

      default:
        aux = "";
        break;
    }
    return fmt::format_to(ctx.out(), "{:04} {}{}{}{}{}", t.location.line,
                          t.type, aux.empty() ? "" : " ", aux,
                          t.text.empty() ? "" : " ",
                          emil::to_std_string(t.text));
  }
};
