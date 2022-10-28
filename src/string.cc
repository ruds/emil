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

#include "emil/string.h"

#include <utf8.h>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iterator>

#include "emil/runtime.h"

namespace emil {

ManagedString::ManagedString() {
  std::memset(&data_, 0, sizeof(data_));
  assert(is_short());
}

ManagedString::ManagedString(std::u8string_view contents) {
  const auto sz = contents.length();
  const auto nc = utf8::distance(contents.begin(), contents.end());
  if (sz <= MAX_SHORT_SIZE) {
    data_.s.double_size = 2 * contents.length();
    data_.s.num_codepoints = static_cast<unsigned char>(nc);
    std::copy(contents.begin(), contents.end(), std::begin(data_.s.data));
    assert(is_short());
  } else {
    auto pb = ctx().mgr->allocate_private_buffer(sz);
    char8_t* buf = reinterpret_cast<char8_t*>(pb.buf());
    std::copy(contents.begin(), contents.end(), buf);
    auto ptr = reinterpret_cast<std::uintptr_t>(buf);
    assert((ptr & STORAGE_FLAG) == 0);
    data_.l.data = ptr | STORAGE_FLAG;
    data_.l.size = sz;
    data_.l.num_codepoints = nc;
    pb.release();
    assert(!is_short());
  }
}

ManagedString::~ManagedString() {
  if (!is_short()) {
    ctx().mgr->free_private_buffer(
        reinterpret_cast<void*>(const_cast<char8_t*>(data())), data_.l.size);
  }
}

ManagedString::operator std::u8string_view() const { return {data(), size()}; }

const char8_t* ManagedString::data() const {
  static const std::uintptr_t CLEAR_STORAGE_FLAG =
      ~static_cast<std::uintptr_t>(STORAGE_FLAG);
  return is_short() ? data_.s.data
                    : reinterpret_cast<const char8_t*>(data_.l.data &
                                                       CLEAR_STORAGE_FLAG);
}

std::size_t ManagedString::size() const {
  return is_short() ? data_.s.double_size / 2 : data_.l.size;
}

std::size_t ManagedString::num_codepoints() const {
  return is_short() ? data_.s.num_codepoints : data_.l.num_codepoints;
}

bool ManagedString::empty() const {
  return !*reinterpret_cast<const unsigned char*>(&data_);
}

bool ManagedString::is_short() const {
  return !(*reinterpret_cast<const unsigned char*>(&data_) & STORAGE_FLAG);
}

StringPtr make_string(std::u8string_view s) {
  return make_managed<ManagedString>(s);
}

bool operator==(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) ==
         static_cast<std::u8string_view>(r);
}

bool operator==(const std::u8string_view& l, const ManagedString& r) {
  return l == static_cast<std::u8string_view>(r);
}

bool operator==(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) == r;
}

bool operator!=(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) !=
         static_cast<std::u8string_view>(r);
}

bool operator!=(const std::u8string_view& l, const ManagedString& r) {
  return l != static_cast<std::u8string_view>(r);
}

bool operator!=(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) != r;
}

bool operator<(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) <
         static_cast<std::u8string_view>(r);
}

bool operator<(const std::u8string_view& l, const ManagedString& r) {
  return l < static_cast<std::u8string_view>(r);
}

bool operator<(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) < r;
}

bool operator<=(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) <=
         static_cast<std::u8string_view>(r);
}

bool operator<=(const std::u8string_view& l, const ManagedString& r) {
  return l <= static_cast<std::u8string_view>(r);
}

bool operator<=(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) <= r;
}

bool operator>(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) >
         static_cast<std::u8string_view>(r);
}

bool operator>(const std::u8string_view& l, const ManagedString& r) {
  return l > static_cast<std::u8string_view>(r);
}

bool operator>(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) > r;
}

bool operator>=(const ManagedString& l, const ManagedString& r) {
  return static_cast<std::u8string_view>(l) >=
         static_cast<std::u8string_view>(r);
}

bool operator>=(const std::u8string_view& l, const ManagedString& r) {
  return l >= static_cast<std::u8string_view>(r);
}

bool operator>=(const ManagedString& l, const std::u8string_view& r) {
  return static_cast<std::u8string_view>(l) >= r;
}

}  // namespace emil
