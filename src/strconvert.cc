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

#include "emil/strconvert.h"

#include <fmt/core.h>
#include <utf8.h>

#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>

namespace emil {

std::u8string to_u8string(std::string_view s) {
  return std::u8string(s.begin(), s.end());
}

void to_u8string(std::string_view s, std::u8string& out) {
  out.append(s.begin(), s.end());
}

std::string to_hex(std::u8string_view s) {
  std::string out;
  to_hex(s, out);
  return out;
}

void to_hex(std::u8string_view s, std::string& out) {
  auto it = back_inserter(out);
  for (char8_t c : s) {
    fmt::format_to(it, "{:02X}", (unsigned int)c);
  }
}

std::string to_std_string(std::u8string_view s) {
  std::string out;
  to_std_string(s, out);
  return out;
}

// Macs don't have the uchar.h header so we have to assume that
// std::string is encoded with utf-8.
void to_std_string(std::u8string_view s, std::string& out) {
  out.append(begin(s), end(s));
}

std::string to_std_string(std::u32string_view s) { return utf8::utf32to8(s); }

void to_std_string(std::u32string_view s, std::string& out) {
  utf8::utf32to8(begin(s), end(s), back_inserter(out));
}

std::string to_std_string(char32_t c) {
  std::string out;
  to_std_string(c, out);
  return out;
}

void to_std_string(char32_t c, std::string& out) {
  if (32 <= c && c < 128) {
    out += static_cast<char>(c);
  } else if (c < 0x10000) {
    out.append(fmt::format(R"(\u{:04X})", static_cast<std::uint32_t>(c)));
  } else {
    out.append(fmt::format(R"(\U{:06X})", static_cast<std::uint32_t>(c)));
  }
}

}  // namespace emil
