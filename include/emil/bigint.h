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

#include <compare>
#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <string>

#include "emil/gc.h"

namespace emil {

namespace testing {
class BigintTestAccessor;
}

/**
 * @brief A multi-precision integer that uses emil's memory manager.
 *
 * The size is limited to (2^31-1) 64-bit words. Numbers greater than
 * -2^64 and less than 2^64 are always stored without further
 * allocation.
 */
class bigint : public Managed {
  struct token {
   private:
    token() {}
    friend bigint;
  };

 public:
  // Never allocates; safe to use in a non-managed context.
  bigint() noexcept;
  ~bigint();
  // Never allocates; safe to use in a non-managed context.
  explicit bigint(std::int64_t value) noexcept;
  bigint(std::uint64_t value, bool is_positive) noexcept;
  /** Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134. */
  bigint(token, PrivateBuffer buf, std::int32_t size) noexcept;

  std::string to_string() const;

  friend bool operator==(const bigint& l, const bigint& r) noexcept;
  friend bool operator==(std::int64_t l, const bigint& r) noexcept;
  friend bool operator==(const bigint& l, std::int64_t r) noexcept;
  friend std::strong_ordering operator<=>(const bigint& l,
                                          const bigint& r) noexcept;
  friend std::strong_ordering operator<=>(std::int64_t l,
                                          const bigint& r) noexcept;
  friend std::strong_ordering operator<=>(const bigint& l,
                                          std::int64_t r) noexcept;

  friend managed_ptr<bigint> operator+(const bigint& l, const bigint& r);
  friend managed_ptr<bigint> operator+(const bigint& l, std::int64_t r);
  friend managed_ptr<bigint> operator+(std::int64_t l, const bigint& r);

  friend managed_ptr<bigint> operator-(const bigint& l, const bigint& r);
  friend managed_ptr<bigint> operator-(const bigint& l, std::int64_t r);
  friend managed_ptr<bigint> operator-(std::int64_t l, const bigint& r);

  friend managed_ptr<bigint> operator*(const bigint& l, const bigint& r);
  friend managed_ptr<bigint> operator*(const bigint& l, std::int64_t r);
  friend managed_ptr<bigint> operator*(std::int64_t l, const bigint& r);

 private:
  friend class testing::BigintTestAccessor;

  union {
    std::uint64_t value;
    std::uint64_t* data;
  } s_;
  std::int32_t size_;
  std::uint32_t capacity_;

  bigint(const bigint& o) = delete;
  bigint& operator=(const bigint& o) = delete;

  bigint(bigint&& o) = delete;
  bigint& operator=(bigint&& o) = delete;

  static token new_token() { return token{}; }
  static std::strong_ordering compare_magnitudes(const bigint& l,
                                                 const bigint& r) noexcept;
  static managed_ptr<bigint> add_magnitudes(const bigint& l, const bigint& r,
                                            bool is_positive);
  static managed_ptr<bigint> subtract_magnitudes(const bigint& l,
                                                 const bigint& r,
                                                 bool is_positive);

  const std::uint64_t* ptr() const;
  void free_buffer();

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override { return sizeof(bigint); }
};

std::ostream& operator<<(std::ostream& os, const bigint& b);
std::ostream& operator<<(std::ostream& os, const managed_ptr<bigint>& b);

/**
 * @brief Adds `l` and `r` with carry.
 *
 * `carry` must be zero or one. The lowest 64 bits of `l + r + carry` are stored
 * in `result`, while the highest bit is stored in `carry`.
 */
void add_with_carry(std::uint64_t l, std::uint64_t r, std::uint64_t& carry,
                    std::uint64_t& result);

/**
 * @brief Subtracts `r` from `l` with borrow.
 *
 * `borrow` must be zero or one. If `r + borrow > l`, the lowest 64
 * bits of `2^64 + l - (r + borrow)` are stored in `result` and
 * `borrow` is set to one. Otherwise, `l - r` is stored in `result`
 * and `borrow` is set to zero.
 */
void sub_with_borrow(std::uint64_t, std::uint64_t r, std::uint64_t& borrow,
                     std::uint64_t& result);

}  // namespace emil
