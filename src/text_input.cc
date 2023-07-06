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

#include "emil/text_input.h"

#include <unicode/uchar.h>
#include <unicode/urename.h>

#include <coroutine>
#include <cstddef>
#include <iostream>
#include <iterator>
#include <optional>
#include <string>

#include "emil/processor.h"

namespace emil {

namespace {

using processor::next_input;
using processor::peek;
using processor::processor_subtask;
using processor::unit;

}  // namespace

processor::processor<unit, char32_t> read_stream(
    std::basic_istream<char32_t>& in) {
  std::istreambuf_iterator<char32_t> it{in};
  const std::istreambuf_iterator<char32_t> end;
  while (it != end) {
    co_yield *it++;
  }
}

processor::processor<unit, char32_t> read_string(std::u32string in) {
  auto it = in.cbegin();
  while (it != in.cend()) {
    co_yield *it++;
  }
}

namespace {

using CharSeqMatcher = processor_subtask<char32_t, bool>;

template <typename CharPtr>
bool is_gcb(CharPtr c, UGraphemeClusterBreak cat) {
  return c && u_getIntPropertyValue(*c, UCHAR_GRAPHEME_CLUSTER_BREAK) == cat;
}

CharSeqMatcher match_crlf(std::u32string& out) {
  const auto c2 = co_await peek{2};
  const auto c1 = co_await peek{};
  if (is_gcb(c1, U_GCB_CR) && is_gcb(c2, U_GCB_LF)) {
    out += co_await next_input{};
    out += co_await next_input{};
    co_return true;
  }
  co_return false;
}

CharSeqMatcher match_precore_seq(std::u32string& out) {
  bool matched = false;
  while (is_gcb(co_await peek{}, U_GCB_PREPEND)) {
    matched = true;
    out += co_await next_input{};
  }
  co_return matched;
}

CharSeqMatcher match_hangul_syllable(std::u32string& out) {
  bool matched_l = false;
  while (is_gcb(co_await peek{}, U_GCB_L)) {
    out += co_await next_input{};
    matched_l = true;
  }
  auto c = co_await peek{};
  bool matched_v = false;
  if (is_gcb(c, U_GCB_V) || is_gcb(c, U_GCB_LV)) {
    matched_v = true;
    out += co_await next_input{};
    while (is_gcb(co_await peek{}, U_GCB_V)) out += co_await next_input{};
  } else if (is_gcb(c, U_GCB_LVT)) {
    matched_v = true;
    out += co_await next_input{};
  }
  if (matched_v) {
    while (is_gcb(co_await peek{}, U_GCB_T)) out += co_await next_input{};
    co_return true;
  } else if (matched_l) {
    co_return true;
  }
  if (is_gcb(c, U_GCB_T)) {
    out += co_await next_input{};
    while (is_gcb(co_await peek{}, U_GCB_T)) out += co_await next_input{};
    co_return true;
  }
  co_return false;
}

CharSeqMatcher match_ri_sequence(std::u32string& out) {
  const auto c2 = co_await peek{2};
  const auto c1 = co_await peek{};
  if (is_gcb(c1, U_GCB_REGIONAL_INDICATOR) &&
      is_gcb(c2, U_GCB_REGIONAL_INDICATOR)) {
    out += co_await next_input{};
    out += co_await next_input{};
    co_return true;
  }
  co_return false;
}

template <typename CharPtr>
bool is_xpicto(CharPtr c) {
  return c && u_hasBinaryProperty(*c, UCHAR_EXTENDED_PICTOGRAPHIC);
}

CharSeqMatcher match_xpicto_sequence(std::u32string& out) {
  if (!is_xpicto(co_await peek{})) co_return false;
  out += co_await next_input{};
  while (1) {
    std::size_t lookahead = 1;
    while (is_gcb(co_await peek{lookahead}, U_GCB_EXTEND)) ++lookahead;
    if (is_gcb(co_await peek{lookahead}, U_GCB_ZWJ) &&
        is_xpicto(co_await peek{lookahead + 1})) {
      for (std::size_t i = 0; i < lookahead + 1; ++i)
        out += co_await next_input{};
    } else {
      co_return true;
    }
  }
}

CharSeqMatcher match_core_noncontrol(std::u32string& out) {
  const auto c = co_await peek{};
  if (!c || is_gcb(c, U_GCB_CONTROL) || is_gcb(c, U_GCB_CR) ||
      is_gcb(c, U_GCB_LF))
    co_return false;
  out += co_await next_input{};
  co_return true;
}

CharSeqMatcher match_core(std::u32string& out) {
  const auto c = co_await peek{};
  if (!c) co_return false;
  if (co_await match_hangul_syllable(out)) co_return true;
  if (co_await match_ri_sequence(out)) co_return true;
  if (co_await match_xpicto_sequence(out)) co_return true;
  co_return co_await match_core_noncontrol(out);
}

processor_subtask<char32_t, void> match_postcore_seq(std::u32string& out) {
  for (auto c = co_await peek{};
       is_gcb(c, U_GCB_EXTEND) || is_gcb(c, U_GCB_ZWJ) ||
       is_gcb(c, U_GCB_SPACING_MARK);
       c = co_await peek{}) {
    out += co_await next_input{};
  }
}

}  // namespace

processor_subtask<char32_t, std::u32string> next_grapheme_cluster() {
  std::u32string out;
  try {
    co_await append_next_grapheme_cluster(out);
  } catch (processor::eof) {
    if (!out.empty()) co_return out;
    throw;
  }
  co_return out;
}

processor_subtask<char32_t, void> append_next_grapheme_cluster(
    std::u32string& out) {
  if (co_await match_crlf(out)) co_return;
  if (is_gcb(co_await peek{}, U_GCB_CONTROL)) {
    out += co_await next_input{};
    co_return;
  }
  const bool matched_precore = co_await match_precore_seq(out);
  if (!co_await peek{}) co_return;
  if (!co_await match_core(out)) {
    if (!matched_precore) out += co_await next_input{};
    co_return;
  }
  co_await match_postcore_seq(out);
}

}  // namespace emil
