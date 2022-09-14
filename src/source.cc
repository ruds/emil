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

#include "emil/source.h"

#include <unicode/uchar.h>
#include <unicode/urename.h>

#include <any>
#include <deque>
#include <istream>
#include <iterator>
#include <memory>
#include <string>
#include <utility>

namespace emil {

using std::cbegin;
using std::cend;

namespace {
template <typename It, std::sentinel_for<It> Sen = It>
class IteratorSource : public Source<> {
 public:
  IteratorSource(It begin, Sen end) : container_(), in_(begin), end_(end) {}
  template <typename T>
  explicit IteratorSource(T&& container)
      : container_(std::forward<T>(container)),
        in_(cbegin(any_cast<T&>(container_))),
        end_(cend(any_cast<T&>(container_))) {}
  ~IteratorSource() override = default;

  char32_t advance() override {
    if (empty(lookahead_buffer_)) {
      return *in_++;
    }
    char32_t c = lookahead_buffer_.front();
    lookahead_buffer_.pop_front();
    return c;
  }

  const char32_t* peek(size_t lookahead) override {
    while (size(lookahead_buffer_) <= lookahead && in_ != end_) {
      lookahead_buffer_.push_back(*in_++);
    }
    if (size(lookahead_buffer_) <= lookahead) {
      return nullptr;
    }
    return &lookahead_buffer_[lookahead];
  }

  bool at_end() const override {
    return empty(lookahead_buffer_) && in_ == end_;
  }

  void putback(char32_t c) override { lookahead_buffer_.push_front(c); }

 private:
  std::any container_;
  It in_;
  Sen end_;
  std::deque<char32_t> lookahead_buffer_;
};

}  // namespace

std::unique_ptr<Source<>> make_source(std::basic_istream<char32_t>& in) {
  return std::make_unique<IteratorSource<std::istreambuf_iterator<char32_t>>>(
      std::istreambuf_iterator<char32_t>{in},
      std::istreambuf_iterator<char32_t>{});
}

std::unique_ptr<Source<>> make_source(std::u32string in) {
  return std::make_unique<IteratorSource<std::u32string::const_iterator>>(
      std::move(in));
}

std::u32string next_grapheme_cluster(Source<>& s) {
  std::u32string out;
  next_grapheme_cluster(s, out);
  return out;
}

namespace {

bool is_gcb(const char32_t* c, UGraphemeClusterBreak cat) {
  return c && u_getIntPropertyValue(*c, UCHAR_GRAPHEME_CLUSTER_BREAK) == cat;
}

bool match_crlf(Source<>& s, std::u32string& out) {
  const auto c1 = s.peek();
  const auto c2 = s.peek(1);
  if (is_gcb(c1, U_GCB_CR) && is_gcb(c2, U_GCB_LF)) {
    out += s.advance();
    out += s.advance();
    return true;
  }
  return false;
}

bool match_precore_seq(Source<>& s, std::u32string& out) {
  bool matched = false;
  while (is_gcb(s.peek(), U_GCB_PREPEND)) {
    matched = true;
    out += s.advance();
  }
  return matched;
}

bool match_hangul_syllable(Source<>& s, std::u32string& out) {
  bool matched_l = false;
  while (is_gcb(s.peek(), U_GCB_L)) {
    out += s.advance();
    matched_l = true;
  }
  auto c = s.peek();
  bool matched_v = false;
  if (is_gcb(c, U_GCB_V) || is_gcb(c, U_GCB_LV)) {
    matched_v = true;
    out += s.advance();
    while (is_gcb(s.peek(), U_GCB_V)) out += s.advance();
  } else if (is_gcb(c, U_GCB_LVT)) {
    matched_v = true;
    out += s.advance();
  }
  if (matched_v) {
    while (is_gcb(s.peek(), U_GCB_T)) out += s.advance();
    return true;
  } else if (matched_l) {
    return true;
  }
  if (is_gcb(c, U_GCB_T)) {
    out += s.advance();
    while (is_gcb(s.peek(), U_GCB_T)) out += s.advance();
    return true;
  }
  return false;
}

bool match_ri_sequence(Source<>& s, std::u32string& out) {
  if (is_gcb(s.peek(), U_GCB_REGIONAL_INDICATOR) &&
      is_gcb(s.peek(1), U_GCB_REGIONAL_INDICATOR)) {
    out += s.advance();
    out += s.advance();
    return true;
  }
  return false;
}

bool is_xpicto(const char32_t* c) {
  return c && u_hasBinaryProperty(*c, UCHAR_EXTENDED_PICTOGRAPHIC);
}

bool match_xpicto_sequence(Source<>& s, std::u32string& out) {
  if (!is_xpicto(s.peek())) return false;
  out += s.advance();
  while (1) {
    std::size_t lookahead = 0;
    while (is_gcb(s.peek(lookahead), U_GCB_EXTEND)) ++lookahead;
    if (is_gcb(s.peek(lookahead), U_GCB_ZWJ) &&
        is_xpicto(s.peek(lookahead + 1))) {
      for (std::size_t i = 0; i < lookahead + 2; ++i) out += s.advance();
    } else {
      return true;
    }
  }
}

bool match_core_noncontrol(Source<>& s, std::u32string& out) {
  const auto c = s.peek();
  if (!c || is_gcb(c, U_GCB_CONTROL) || is_gcb(c, U_GCB_CR) ||
      is_gcb(c, U_GCB_LF))
    return false;
  out += s.advance();
  return true;
}

bool match_core(Source<>& s, std::u32string& out) {
  const auto c = s.peek();
  if (!c) return false;
  if (match_hangul_syllable(s, out)) return true;
  if (match_ri_sequence(s, out)) return true;
  if (match_xpicto_sequence(s, out)) return true;
  return match_core_noncontrol(s, out);
}

void match_postcore_seq(Source<>& s, std::u32string& out) {
  for (auto c = s.peek(); is_gcb(c, U_GCB_EXTEND) || is_gcb(c, U_GCB_ZWJ) ||
                          is_gcb(c, U_GCB_SPACING_MARK);
       c = s.peek()) {
    out += s.advance();
  }
}
}  // namespace

void next_grapheme_cluster(Source<>& s, std::u32string& out) {
  if (match_crlf(s, out)) return;
  if (is_gcb(s.peek(), U_GCB_CONTROL)) {
    out += s.advance();
    return;
  }
  const bool matched_precore = match_precore_seq(s, out);
  if (s.at_end()) return;
  if (!match_core(s, out)) {
    if (!matched_precore) out += s.advance();
    return;
  }
  match_postcore_seq(s, out);
}

}  // namespace emil
