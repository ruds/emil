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

#include <any>
#include <deque>
#include <istream>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <utility>

namespace emil {

using std::cbegin;
using std::cend;

namespace {
template <typename It, std::sentinel_for<It> Sen = It>
class IteratorSource : public Source {
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

  std::optional<char32_t> peek(size_t lookahead) override {
    while (size(lookahead_buffer_) <= lookahead && in_ != end_) {
      lookahead_buffer_.push_back(*in_++);
    }
    if (size(lookahead_buffer_) <= lookahead) {
      return {};
    }
    return lookahead_buffer_[lookahead];
  }

  bool at_end() const override {
    return empty(lookahead_buffer_) && in_ == end_;
  }

 private:
  std::any container_;
  It in_;
  Sen end_;
  std::deque<char32_t> lookahead_buffer_;
};
}  // namespace

std::unique_ptr<Source> make_source(std::basic_istream<char32_t>& in) {
  return std::make_unique<IteratorSource<std::istreambuf_iterator<char32_t>>>(
      std::istreambuf_iterator<char32_t>{in},
      std::istreambuf_iterator<char32_t>{});
}

std::unique_ptr<Source> make_source(std::u32string in) {
  return std::make_unique<IteratorSource<std::u32string::const_iterator>>(
      std::move(in));
}

}  // namespace emil
