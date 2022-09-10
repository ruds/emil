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

#include <cstdlib>
#include <istream>
#include <memory>
#include <optional>
#include <string>

namespace emil {

/** A source of characters to feed into the lexer. */
class Source {
 public:
  virtual ~Source() = default;
  virtual char32_t advance() = 0;
  virtual std::optional<char32_t> peek(std::size_t lookahead = 0) = 0;
  virtual bool at_end() const = 0;
  /**
   * Implementations must permit at least one character of putback.
   *
   * Behavior is unspecified if `c` is not the same as the character
   * most recently returned by `advance`.
   */
  virtual void putback(char32_t c) = 0;
};

/** Advances `s` past the next grapheme cluster and returns it. */
std::u32string next_grapheme_cluster(Source& s);

/** Advances `s` past the next grapheme cluster and appends it to `out`. */
void next_grapheme_cluster(Source& s, std::u32string& out);

std::unique_ptr<Source> make_source(std::basic_istream<char32_t>& in);
std::unique_ptr<Source> make_source(std::u32string in);

}  // namespace emil
