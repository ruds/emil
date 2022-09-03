#pragma once

#include <cstdint>
#include <stdexcept>
#include <string>
#include <string_view>
#include <variant>

#include "bigint.h"
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
  DECLARE(FSTRING_IEXPR_F, X)

ENUM_WITH_TEXT(TokenType, TOKEN_TYPE_LIST)

using token_auxiliary_t = std::variant<std::monostate, int64_t, bigint, double,
                                       char32_t, std::u8string>;

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

      case TokenType::CHAR:
        aux = format("{:06X}", (std::uint32_t)get<char32_t>(t.aux));
        break;

      default:
        throw std::runtime_error("Unhandled token type.");
    }
    return fmt::format_to(ctx.out(), "{:04} {}{}{}{}{}", t.line, t.type,
                          aux.empty() ? "" : " ", aux,
                          t.text.empty() ? "" : " ", utf8::utf32to8(t.text));
  }
};
