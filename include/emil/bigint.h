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
#include <string_view>
#include <utility>

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
 * allocation (this is similar to the small string optimization).
 *
 * All operations on this class are non-modifying.
 */
class bigint : public Managed {
  struct token {
   private:
    token() {}
    friend bigint;
  };

 public:
  /** Never allocates; safe to use in a non-managed context. */
  bigint() noexcept;
  /** Never allocates; safe to use in a non-managed context. */
  explicit bigint(std::int64_t value) noexcept;
  /** Never allocates; safe to use in a non-managed context. */
  bigint(std::uint64_t value, bool is_positive) noexcept;

  /**
   * @brief Produces a bigint with absolute value (hi << 64) + lo.
   *
   * Always allocates; not safe to use in a non-managed context.
   */
  bigint(std::uint64_t hi, std::uint64_t lo, bool is_positive);
  /**
   * @brief Produces a bigint with the same value as o.
   *
   * Allocates whenever abs(o) >= 2^64; not safe to use in a
   * non-managed context. Generally you should prefer to copy the
   * managed_ptr to o instead.
   */
  bigint(const bigint& o);
  /**
   * @brief Takes ownership of buf.
   *
   * Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134.
   */
  bigint(token, PrivateBuffer buf, std::int32_t size) noexcept;

  ~bigint();

  /** Produces the value of this bigint in hex. */
  std::string to_std_string() const;
  std::u8string to_string() const;

  friend bool operator==(const bigint& l, const bigint& r) noexcept;
  friend bool operator==(std::int64_t l, const bigint& r) noexcept;
  friend bool operator==(const bigint& l, std::int64_t r) noexcept;
  friend std::strong_ordering operator<=>(const bigint& l,
                                          const bigint& r) noexcept;
  friend std::strong_ordering operator<=>(std::int64_t l,
                                          const bigint& r) noexcept;
  friend std::strong_ordering operator<=>(const bigint& l,
                                          std::int64_t r) noexcept;

  /** May throw std::overflow_error. */
  friend managed_ptr<bigint> operator+(const bigint& l, const bigint& r);
  /** @overload */
  friend managed_ptr<bigint> operator+(const bigint& l, std::int64_t r);
  /** @overload */
  friend managed_ptr<bigint> operator+(std::int64_t l, const bigint& r);

  /** May throw std::overflow_error. */
  friend managed_ptr<bigint> operator-(const bigint& l, const bigint& r);
  /** @overload */
  friend managed_ptr<bigint> operator-(const bigint& l, std::int64_t r);
  /** @overload */
  friend managed_ptr<bigint> operator-(std::int64_t l, const bigint& r);

  friend managed_ptr<bigint> operator-(const bigint& b);

  /** May throw std::overflow_error. */
  friend managed_ptr<bigint> operator*(const bigint& l, const bigint& r);
  /** @overload */
  friend managed_ptr<bigint> operator*(const bigint& l, std::int64_t r);
  /** @overload */
  friend managed_ptr<bigint> operator*(std::int64_t l, const bigint& r);

  /** May throw std::overflow_error. */
  friend managed_ptr<bigint> operator<<(const bigint& l, std::uint64_t r);
  friend managed_ptr<bigint> operator>>(const bigint& l, std::uint64_t r);

  /**
   * @brief Returns the quotient and remainder when dividing this by divisor.
   *
   * Returns q and r such that (this = (divisor * q) + r), r is
   * between 0 (inclusive) and divisor (exclusive), and q is (this /
   * divisor) rounded toward 0.
   *
   * Throws domain_error if divisor is zero.
   */
  std::pair<managed_ptr<bigint>, managed_ptr<bigint>> divmod(
      const bigint& divisor) const;

  /**
   * @brief Converts a string with an optional leading '-' followed by a
   * non-empty sequence of '0' and '1' into a bigint.
   *
   * Throws std::overflow_error if the number cannot be represented as a
   * bigint. Throws std::invalid_argument if a '-' is encountered at any
   * location other than the first character or if any other character
   * besides a '0' or '1' is present, or if there are no binary digits.
   */
  friend managed_ptr<bigint> parse_bigint_binary(std::u8string_view num);

  /**
   * @brief Converts a string with an optional leading '-' followed by a
   * non-empty sequence of '0'-'7' into a bigint.
   *
   * Throws std::overflow_error if the number cannot be represented as a
   * bigint. Throws std::invalid_argument if a '-' is encountered at any
   * location other than the first character or if any other character
   * besides '0'-'7' is present, or if there are no octal digits.
   */
  friend managed_ptr<bigint> parse_bigint_octal(std::u8string_view num);

  /**
   * @brief Converts a string with an optional leading '-' followed by a
   * non-empty sequence of '0'-'9' into a bigint.
   *
   * Throws std::overflow_error if the number cannot be represented as a
   * bigint. Throws std::invalid_argument if a '-' is encountered at any
   * location other than the first character or if any other character
   * besides '0'-'9' is present, or if there are no decimal digits.
   */
  friend managed_ptr<bigint> parse_bigint_decimal(std::u8string_view num);

  /**
   * @brief Converts a string with an optional leading '-' followed by a
   * non-empty sequence of '0'-'9'/'a'-'f'/'A'-'F' into a bigint.
   *
   * Throws std::overflow_error if the number cannot be represented as a
   * bigint. Throws std::invalid_argument if a '-' is encountered at any
   * location other than the first character or if any other character
   * besides a hex digit is present, or if there are no hex digits.
   */
  friend managed_ptr<bigint> parse_bigint_hex(std::u8string_view num);

 private:
  friend class testing::BigintTestAccessor;

  // If capacity is 0, we use value; otherwise we use data. In either
  // case, we store the absolute value of the number we represent.
  //
  // data[0] is the least significant word of the value;
  // data[abs(size) - 1] is the most significant word.
  union {
    std::uint64_t value;
    std::uint64_t* data;
  } s_;
  // The absolute value of size_ is the number of words in the value.
  // The sign of size_ is the sign of the value.
  std::int32_t size_;
  // The number of words allocated in the data buffer. This is never 1
  // (1-word numbers are guaranteed to be stored in s_.value, not a
  // separate buffer).
  std::uint32_t capacity_;

  // yagni
  bigint& operator=(const bigint& o) = delete;

  bigint(bigint&& o) = delete;
  bigint& operator=(bigint&& o) = delete;

  // Used by friend functions to access the "private" constructor.
  static token new_token() { return token{}; }

  /** Compares the absolute value of l to r. */
  static std::strong_ordering compare_magnitudes(const bigint& l,
                                                 const bigint& r) noexcept;
  /**
   * Adds the absolute values of l and r, and applies the sign indicated.
   */
  static managed_ptr<bigint> add_magnitudes(const bigint& l, const bigint& r,
                                            bool is_positive);
  /**
   * @brief Subtracts abs(r) from abs(l), applying the sign indicated.
   *
   * Requires abs(l) >= abs(r).
   */
  static managed_ptr<bigint> subtract_magnitudes(const bigint& l,
                                                 const bigint& r,
                                                 bool is_positive);

  /**
   * @brief A pointer to the least significant word of the value.
   *
   * Valid even if capacity_ == 0.
   */
  const std::uint64_t* ptr() const;
  /** Frees s_.data, if it is an allocation. */
  void free_buffer();

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override { return sizeof(bigint); }
};

/** Writes b as a hex value. */
std::ostream& operator<<(std::ostream& os, const bigint& b);
/** Writes *b as a hex value. */
std::ostream& operator<<(std::ostream& os, const managed_ptr<bigint>& b);

managed_ptr<bigint> parse_bigint_binary(std::u8string_view num);
managed_ptr<bigint> parse_bigint_octal(std::u8string_view num);
managed_ptr<bigint> parse_bigint_decimal(std::u8string_view num);
managed_ptr<bigint> parse_bigint_hex(std::u8string_view num);

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
void sub_with_borrow(std::uint64_t l, std::uint64_t r, std::uint64_t& borrow,
                     std::uint64_t& result);

}  // namespace emil
