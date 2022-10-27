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

#include <bit>
#include <cstddef>
#include <cstdint>
#include <string_view>

#include "emil/gc.h"

namespace emil {

/**
 * A utf-8 string managed by the runtime.
 *
 * Uses the short string optimization; strings of 14 bytes or fewer
 * are stored with automatic duration -- that is, without further
 * allocations.
 *
 * Strings are not guaranteed to be zero-terminated.
 */
class ManagedString : public Managed {
 public:
  ManagedString();
  /** Throws if contents are not valid utf-8. */
  explicit ManagedString(std::u8string_view contents);
  ~ManagedString();

  operator std::u8string_view() const;
  const char8_t* data() const;
  std::size_t size() const;
  std::size_t num_codepoints() const;
  bool empty() const;

 private:
  static const std::size_t DATA_SIZE = 16;
  static const std::size_t MAX_SHORT_SIZE = 14;
  static const unsigned char STORAGE_FLAG = 1;

  /** Strings longer than MAX_SHORT_SIZE use this storage layout. */
  struct long_str {
    /** A pointer to the data buffer with the lowest-order bit set to 1,
     * signalling a long string. */
    std::uintptr_t data;
    /** The number of bytes in the string (and buffer). */
    std::uint32_t size;
    /** The number of unicode codepoints in the string. */
    std::uint32_t num_codepoints;
  };
  static_assert(sizeof(long_str) == DATA_SIZE);

  /**
   * Strings not longer than MAX_SHORT_SIZE use this storage layout.
   *
   * Notably, the empty string can be represented as all zeros.
   */
  struct short_str {
    /** Twice the size of the string in bytes (this allows the lowest-order bit
     * always to be zero, signalling a short string). */
    unsigned char double_size;
    /** The number of unicode codepoints in the string. */
    unsigned char num_codepoints;
    /** The data buffer. */
    char8_t data[MAX_SHORT_SIZE];
  };
  static_assert(sizeof(short_str) == DATA_SIZE);
  static_assert(std::endian::native == std::endian::little);

  union {
    long_str l;
    short_str s;
  } data_;

  static_assert(sizeof(data_) == DATA_SIZE);

  bool is_short() const;

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedString);
  }
};

managed_ptr<ManagedString> make_string(std::u8string_view s = u8"");

bool operator==(const ManagedString& l, const ManagedString& r);
bool operator==(const std::u8string_view& l, const ManagedString& r);
bool operator==(const ManagedString& l, const std::u8string_view& r);

bool operator!=(const ManagedString& l, const ManagedString& r);
bool operator!=(const std::u8string_view& l, const ManagedString& r);
bool operator!=(const ManagedString& l, const std::u8string_view& r);

bool operator<(const ManagedString& l, const ManagedString& r);
bool operator<(const std::u8string_view& l, const ManagedString& r);
bool operator<(const ManagedString& l, const std::u8string_view& r);

bool operator<=(const ManagedString& l, const ManagedString& r);
bool operator<=(const std::u8string_view& l, const ManagedString& r);
bool operator<=(const ManagedString& l, const std::u8string_view& r);

bool operator>(const ManagedString& l, const ManagedString& r);
bool operator>(const std::u8string_view& l, const ManagedString& r);
bool operator>(const ManagedString& l, const std::u8string_view& r);

bool operator>=(const ManagedString& l, const ManagedString& r);
bool operator>=(const std::u8string_view& l, const ManagedString& r);
bool operator>=(const ManagedString& l, const std::u8string_view& r);

}  // namespace emil
