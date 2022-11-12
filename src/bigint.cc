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

#include "emil/bigint.h"

#include <algorithm>
#include <cassert>
#include <compare>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iomanip>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

#include "emil/gc.h"
#include "emil/runtime.h"

namespace emil {

namespace {

constexpr const std::uint64_t BI_WORD_MAX =
    std::numeric_limits<std::uint64_t>::max();
constexpr const std::uint32_t BI_SIZE_MAX =
    std::numeric_limits<std::int32_t>::max();

/** Takes the absolute value of v. Safe to use on LONG_MIN. */
std::uint64_t uabs(std::int64_t v) {
  return v < 0 ? -static_cast<std::uint64_t>(v) : v;
}

std::int32_t bigint_size(std::int64_t v) {
  if (v > 0)
    return 1;
  else if (v < 0)
    return -1;
  else
    return 0;
}

}  // namespace

bigint::bigint() noexcept : s_{.value = 0}, size_(0), capacity_(0) {}

bigint::bigint(const bigint& o)
    : size_(o.size_), capacity_(o.capacity_ ? uabs(o.size_) : 0) {
  if (capacity_) {
    auto pbuf = ctx().mgr->allocate_private_buffer(capacity_ * 8ull);
    std::memcpy(pbuf.buf(), o.s_.data, capacity_ * 8ull);
    s_.data = reinterpret_cast<std::uint64_t*>(pbuf.release());
  } else {
    s_.value = o.s_.value;
  }
}

bigint::bigint(std::int64_t value) noexcept
    : s_{.value = uabs(value)}, size_(bigint_size(value)), capacity_(0) {}

bigint::bigint(std::uint64_t value, bool is_positive) noexcept
    : s_{.value = value},
      size_(value ? is_positive ? 1 : -1 : 0),
      capacity_(0) {}

bigint::bigint(std::uint64_t hi, std::uint64_t lo, bool is_positive)
    : bigint(token(), ctx().mgr->allocate_private_buffer(16),
             is_positive ? 2 : -2) {
  s_.data[0] = lo;
  s_.data[1] = hi;
}

bigint::bigint(token, PrivateBuffer buf, std::int32_t size) noexcept
    : size_(size), capacity_(buf.size() / 8) {
  assert(buf.size() % 8 == 0);
  s_.data = reinterpret_cast<std::uint64_t*>(buf.release());
}

bigint::~bigint() { free_buffer(); }

std::string bigint::to_string() const {
  if (!size_) return "0";
  std::ostringstream os;
  if (size_ < 0) os << "-";
  os << std::hex << std::uppercase;
  if (!capacity_) {
    os << s_.value;
    return os.str();
  }
  auto len = uabs(size_);
  os << s_.data[len - 1];
  os << std::setfill('0');
  for (std::uint_fast32_t i = len - 1; i > 0; --i) {
    os << std::setw(16) << s_.data[i - 1];
  }
  return os.str();
}

bool operator==(const bigint& l, const bigint& r) noexcept {
  if (l.size_ != r.size_) return false;
  assert(l.capacity_ != 1);
  assert(r.capacity_ != 1);
  if (l.capacity_) {
    assert(r.capacity_);
    const auto s = uabs(l.size_);
    for (std::uint_fast32_t i = 0; i < s; ++i) {
      if (l.s_.data[i] != r.s_.data[i]) return false;
    }
    return true;
  }
  assert(!r.capacity_);
  return l.s_.value == r.s_.value;
}

bool operator==(std::int64_t l, const bigint& r) noexcept {
  return bigint(l) == r;
}

bool operator==(const bigint& l, std::int64_t r) noexcept {
  return l == bigint(r);
}

std::strong_ordering bigint::compare_magnitudes(const bigint& l,
                                                const bigint& r) noexcept {
  const auto ls = uabs(l.size_);
  const auto rs = uabs(r.size_);
  if (ls != rs) return ls <=> rs;
  if (l.capacity_) {
    assert(r.capacity_ > 1);
    assert(l.capacity_ > 1);
    for (std::uint_fast32_t i = ls; i > 0; --i) {
      const auto ld = l.s_.data[i - 1];
      const auto rd = r.s_.data[i - 1];
      if (ld != rd) return ld <=> rd;
    }
    return std::strong_ordering::equal;
  }
  assert(!r.capacity_);
  return l.s_.value <=> r.s_.value;
}

std::strong_ordering operator<=>(const bigint& l, const bigint& r) noexcept {
  if (l.size_ != r.size_) return l.size_ <=> r.size_;
  auto order = bigint::compare_magnitudes(l, r);
  return l.size_ >= 0 ? order : (0 <=> order);
}

std::strong_ordering operator<=>(std::int64_t l, const bigint& r) noexcept {
  return bigint(l) <=> r;
}

std::strong_ordering operator<=>(const bigint& l, std::int64_t r) noexcept {
  return l <=> bigint(r);
}

std::ostream& operator<<(std::ostream& os, const bigint& b) {
  return os << b.to_string();
}

std::ostream& operator<<(std::ostream& os, const managed_ptr<bigint>& b) {
  return os << b->to_string();
}

namespace {

/**
 * @brief Add the absolute values of two bigints.
 *
 * Requires that ln or rn is greater than 1 to prevent allocation in
 * case the size of the sum fits in one word. Aways allocates, so
 * requires a hold on the memory manager.
 */
std::pair<PrivateBuffer, std::uint32_t> add_bufs(const std::uint64_t* l,
                                                 std::uint32_t ln,
                                                 const std::uint64_t* r,
                                                 std::uint32_t rn) {
  assert(ln > 1 || rn > 1);
  const auto* lend = l + ln;
  const auto* rend = r + rn;
  std::size_t capacity;
  // The only way l + r is larger than l or r is if (a) the sum of
  // the highest words of l and r overflow a word or (b) they fill
  // the highest word and there is a carry from the lower words.
  // We're OK with an extra word of allocation in case (b)'s first
  // condition is true but we don't end up with a carry.
  if (ln < rn) {
    capacity = rn;
    if (r[rn - 1] == BI_WORD_MAX) [[unlikely]]
      ++capacity;
  } else if (rn < ln) {
    capacity = ln;
    if (l[ln - 1] == BI_WORD_MAX) [[unlikely]]
      ++capacity;
  } else {
    capacity = ln;
    unsigned __int128 s = r[rn - 1];
    s += l[ln - 1];
    if (s >= BI_WORD_MAX) ++capacity;
  }
  auto buf = ctx().mgr->allocate_private_buffer(capacity * 8ull);
  std::uint64_t* out = reinterpret_cast<std::uint64_t*>(buf.buf());
  std::uint64_t carry = 0;
  std::uint32_t len = 0;
  // The basic idea: while there's words left in both addends, add a
  // word from the left to a word from the right with carry, starting
  // at the least significant word. When one runs out and there's
  // still carry, add words from the longer one with a carry. Once
  // there's no more carry, we can just copy the words from the longer
  // addend to the sum.
  while (l < lend && r < rend) {
    add_with_carry(*l, *r, carry, *out);
    ++l;
    ++r;
    ++out;
    ++len;
  }
  if (ln > rn) {
    while (carry && l < lend) {
      add_with_carry(*l, 0, carry, *out);
      ++l;
      ++out;
      ++len;
    }
    const auto n = lend - l;
    std::memcpy(out, l, n * 8ull);
    out += n;
    len += n;
  } else {
    while (carry && r < rend) {
      add_with_carry(0, *r, carry, *out);
      ++r;
      ++out;
      ++len;
    }
    const auto n = rend - r;
    std::memcpy(out, r, n * 8ull);
    out += n;
    len += n;
  }
  // If we've run out of words in the addends and there's still carry,
  // add a 1 to the sum as an additional word.
  if (carry) {
    *out = 1;
    ++len;
  }
  assert(len == capacity || len + 1 == capacity);
  return std::make_pair(std::move(buf), len);
}

/**
 * @brief Subtract the absolute value of r from the absolute value of l.
 *
 * Requires ln is greater than one. Always allocates, so requires a
 * hold on the memory manager.
 */
std::pair<PrivateBuffer, std::uint32_t> sub_bufs(const std::uint64_t* l,
                                                 std::uint32_t ln,
                                                 const std::uint64_t* r,
                                                 std::uint32_t rn) {
  assert(rn <= ln);
  assert(ln > 1);
  const auto* lend = l + ln;
  const auto* rend = r + rn;
  auto buf = ctx().mgr->allocate_private_buffer(ln * 8ull);
  std::uint64_t* out = reinterpret_cast<std::uint64_t*>(buf.buf());
  std::uint64_t borrow = 0;
  std::uint32_t len = 0;
  // The basic idea: Starting from the least significant word,
  // subtract a word of r from the corresponding word of l with
  // borrow, until we run out of words of r. Then, as long as there's
  // still borrow, subtract 1 from words of l. Then copy the remaining
  // words of l into the difference.
  while (r < rend) {
    sub_with_borrow(*l, *r, borrow, *out);
    ++l;
    ++r;
    ++out;
    ++len;
  }
  while (borrow && l < lend) {
    sub_with_borrow(*l, 0, borrow, *out);
    ++l;
    ++out;
    ++len;
  }
  const auto n = lend - l;
  std::memcpy(out, l, n * 8ull);
  out += n;
  len += n;
  while (!*--out) --len;
  assert(len >= 1);
  return std::make_pair(std::move(buf), len);
}

}  // namespace

const std::uint64_t* bigint::ptr() const {
  return capacity_ ? s_.data : &s_.value;
}

managed_ptr<bigint> bigint::add_magnitudes(const bigint& l, const bigint& r,
                                           bool is_positive) {
  if (l.capacity_ || r.capacity_) {
    auto hold = ctx().mgr->acquire_hold();
    auto result = add_bufs(l.ptr(), uabs(l.size_), r.ptr(), uabs(r.size_));
    if (result.second > BI_SIZE_MAX) {
      throw std::overflow_error("Overflow when adding or subtracting bigints");
    }
    return make_managed<bigint>(token{}, std::move(result.first),
                                is_positive ? result.second : -result.second);
  }
  // Both addends fit into a single word.
  std::uint64_t sum;
  std::uint64_t carry = 0;
  add_with_carry(l.s_.value, r.s_.value, carry, sum);
  if (carry) {
    return make_managed<bigint>(1, sum, is_positive);
  } else {
    return make_managed<bigint>(sum, is_positive);
  }
}

managed_ptr<bigint> bigint::subtract_magnitudes(const bigint& l,
                                                const bigint& r,
                                                bool is_positive) {
  if (l.capacity_) {
    auto hold = ctx().mgr->acquire_hold();
    auto result = sub_bufs(l.ptr(), uabs(l.size_), r.ptr(), uabs(r.size_));
    if (result.second > BI_SIZE_MAX) {
      throw std::overflow_error("Overflow when adding or subtracting bigints");
    }
    if (result.second == 1) {
      return make_managed<bigint>(
          *reinterpret_cast<std::uint64_t*>(result.first.buf()), is_positive);
    }
    return make_managed<bigint>(token{}, std::move(result.first),
                                is_positive ? result.second : -result.second);
  }
  // The minuend and subtrahend both fit into a single word.
  return make_managed<bigint>(l.s_.value - r.s_.value, is_positive);
}

managed_ptr<bigint> operator+(const bigint& l, const bigint& r) {
  // The basic idea: if both are positive or both are negative, add
  // together the magnitudes and apply the correct sign. On the other
  // hand, if the signs differ, subtract the smaller magnitude from
  // the greater magnitude and apply the correct sign.
  if ((l.size_ >= 0 && r.size_ >= 0) || (l.size_ <= 0 && r.size_ <= 0)) {
    return bigint::add_magnitudes(l, r, l.size_ > 0 || r.size_ > 0);
  } else {
    auto c = bigint::compare_magnitudes(l, r);
    if (c == 0) {
      return make_managed<bigint>();
    } else if (c > 0) {
      return bigint::subtract_magnitudes(l, r, l.size_ > 0);
    } else {
      return bigint::subtract_magnitudes(r, l, r.size_ > 0);
    }
  }
}

managed_ptr<bigint> operator+(const bigint& l, std::int64_t r) {
  return l + bigint(r);
}

managed_ptr<bigint> operator+(std::int64_t l, const bigint& r) {
  return bigint(l) + r;
}

managed_ptr<bigint> operator-(const bigint& l, const bigint& r) {
  // The basic idea: If the both are positive or both are negative,
  // subtract the smaller magnitude from the greater magnitude and
  // apply the correct sign. Otherwise, add the magnitudes together
  // and apply the correct sign.
  if ((l.size_ > 0 && r.size_ > 0) || (l.size_ < 0 && r.size_ < 0)) {
    auto c = bigint::compare_magnitudes(l, r);
    if (c == 0) {
      return make_managed<bigint>();
    } else {
      if (c > 0) {
        return bigint::subtract_magnitudes(l, r, l.size_ > 0);
      } else {
        return bigint::subtract_magnitudes(r, l, l.size_ < 0);
      }
    }
  } else {
    return bigint::add_magnitudes(l, r, l.size_ > 0 || r.size_ < 0);
  }
}

managed_ptr<bigint> operator-(const bigint& l, std::int64_t r) {
  return l - bigint(r);
}

managed_ptr<bigint> operator-(std::int64_t l, const bigint& r) {
  return bigint(l) - r;
}

managed_ptr<bigint> operator-(const bigint& b) {
  auto neg = make_managed<bigint>(b);
  neg->size_ = -neg->size_;
  return neg;
}

managed_ptr<bigint> operator*(const bigint& l, const bigint& r) {
  // When both l and r fit in a single word, we can do the
  // multiplication using 128-bit integers. When they don't, we
  // multiply l by each word of r and add the results.
  const auto m = uabs(l.size_);
  const auto n = uabs(r.size_);
  const std::int32_t sign = (l.size_ >= 0) == (r.size_ >= 0) ? 1 : -1;
  if (m == 0 || n == 0) return make_managed<bigint>();
  if (m <= 1 && n <= 1) {
    unsigned __int128 p = l.s_.value;
    p *= r.s_.value;
    if (p > BI_WORD_MAX) {
      return make_managed<bigint>(p >> 64, p & BI_WORD_MAX, sign > 0);
    }
    return make_managed<bigint>(static_cast<std::uint64_t>(p), sign > 0);
  }
  auto hold = ctx().mgr->acquire_hold();
  const auto plen = m + n;
  assert(plen > 2);
  // the length may still be legal when plen == BI_SIZE_MAX since the
  // top word may be zero, so we do the multiplication before
  // reporting overflow.
  if (plen > BI_SIZE_MAX + 1) {
    throw std::overflow_error("Overflow when multiplying bigints");
  }
  auto pbuf = ctx().mgr->allocate_private_buffer(plen * 8ull);
  auto* w = reinterpret_cast<std::uint64_t*>(pbuf.buf());
  const std::uint64_t* const u = l.ptr();
  const std::uint64_t* const v = r.ptr();
  // This is based on Knuth's Algorithm M from section 4.3.1 of Volume
  // 2 of the Art of Computer Programming.
  std::memset(w, 0, m * 8ull);
  for (std::uint_fast32_t j = 0; j < n; ++j) {
    std::uint64_t carry = 0;
    for (std::uint_fast32_t i = 0; i < m; ++i) {
      unsigned __int128 t = u[i];
      t *= v[j];
      t += w[i + j];
      t += carry;
      w[i + j] = t & BI_WORD_MAX;
      carry = t >> 64;
    }
    w[j + m] = carry;
  }
  const std::uint32_t len = w[plen - 1] ? plen : plen - 1;
  if (len > BI_SIZE_MAX) {
    throw std::overflow_error("Overflow when multiplying bigints");
  }
  return make_managed<bigint>(bigint::new_token(), std::move(pbuf),
                              static_cast<std::int32_t>(len) * sign);
}

managed_ptr<bigint> operator*(const bigint& l, std::int64_t r) {
  return l * bigint(r);
}

managed_ptr<bigint> operator*(std::int64_t l, const bigint& r) {
  return r * bigint(l);
}

managed_ptr<bigint> operator<<(const bigint& l, std::uint64_t r) {
  // The low 6 bits of r tell us how many bits each word is shifted
  // by, and the high 58 bits tell us how many words of zeros are
  // added as new least-significant words to the number. These new
  // words can be filled in with memset.
  if (!l.size_) return make_managed<bigint>();
  const std::uint64_t word_shift = r / 64;
  const std::uint64_t lbit_shift = r % 64;
  const std::uint64_t rbit_shift = 64 - r;
  const auto lsize = uabs(l.size_);
  // Do we shift any ones out of the current most-significant word
  // into a new word?
  const std::uint64_t topword =
      lbit_shift ? (l.ptr()[lsize - 1] >> rbit_shift) : 0ull;
  const std::uint64_t size = word_shift + lsize + (topword != 0);
  if (size > BI_SIZE_MAX) {
    throw std::overflow_error("Overflow when left-shifting bigint.");
  }
  if (size == 1) {
    return make_managed<bigint>(l.s_.value << lbit_shift, l.size_ > 0);
  }
  auto hold = ctx().mgr->acquire_hold();
  auto pbuf = ctx().mgr->allocate_private_buffer(size * 8ull);
  auto* out = reinterpret_cast<std::uint64_t*>(pbuf.buf());
  std::memset(out, 0, word_shift * 8ull);
  if (lbit_shift) {
    out[word_shift] = l.ptr()[0] << lbit_shift;
    for (std::uint_fast32_t i = 1; i < lsize; ++i) {
      out[word_shift + i] =
          (l.ptr()[i - 1] >> rbit_shift) + (l.ptr()[i] << lbit_shift);
    }
    if (topword) out[size - 1] = topword;
  } else {
    std::memcpy(out + word_shift, l.ptr(), lsize * 8ull);
  }
  return make_managed<bigint>(bigint::new_token(), std::move(pbuf),
                              l.size_ > 0 ? size : -size);
}

managed_ptr<bigint> operator>>(const bigint& l, std::uint64_t r) {
  // The low 6 bits of r tell us how many bits each word is shifted
  // by, and the high 58 bits tell us how many of the least
  // significant words of l are completely dropped.
  if (!l.size_) return make_managed<bigint>();
  const std::uint64_t word_shift = r / 64;
  const auto lsize = uabs(l.size_);
  if (word_shift >= lsize) return make_managed<bigint>();

  const std::uint64_t rbit_shift = r % 64;
  const std::uint64_t lbit_shift = 64 - r;
  // Is the most significant word losing all its ones?
  const std::uint64_t topword = l.ptr()[lsize - 1] >> rbit_shift;

  const std::uint64_t size = lsize - word_shift - (topword == 0);
  if (size == 0) return make_managed<bigint>();
  if (size == 1)
    return topword
               ? make_managed<bigint>(topword, l.size_ > 0)
               : make_managed<bigint>((l.ptr()[lsize - 1] << lbit_shift) +
                                          (l.ptr()[lsize - 2] >> rbit_shift),
                                      l.size_ > 0);

  auto hold = ctx().mgr->acquire_hold();
  auto pbuf = ctx().mgr->allocate_private_buffer(size * 8ull);
  auto* out = reinterpret_cast<std::uint64_t*>(pbuf.buf());
  if (rbit_shift) {
    for (std::uint_fast32_t i = 0; word_shift + i + 1 < lsize; ++i) {
      out[i] = (l.ptr()[word_shift + i] >> rbit_shift) +
               (l.ptr()[word_shift + i + 1] << lbit_shift);
    }
    if (topword) out[size - 1] = topword;
  } else {
    std::memcpy(out, l.ptr() + word_shift, size * 8ull);
  }
  return make_managed<bigint>(bigint::new_token(), std::move(pbuf),
                              l.size_ > 0 ? size : -size);
}

namespace {

/**
 * @brief Subtracts (factor * (val(mul_buf)) << lshift) from val(cbuf) (in
 * place).
 *
 * Requirements:
 * 1. cbuf is a circular buffer of n + 1 words.
 * 2. the least significant word of val(cbuf) is at cbuf[cbuf_start].
 * 3. mul_buf is a buffer of n words.
 * 4. 0 <= lshift < 64
 * 5. (mul_buf[n-1] << lshift) < 2^64
 *
 * Returns true if factor * (val(mul_buf) << lshift) > val(cbuf), in
 * which case val(cbuf) is now 2^(64 * (n + 1)) more than the
 * difference (i.e. is a negative number in (2^64)s-complement).
 */
bool subtract_product_from_circular_buf(std::uint64_t* cbuf,
                                        std::uint_fast32_t cbuf_start,
                                        std::uint64_t factor,
                                        const std::uint64_t* mul_buf,
                                        std::uint32_t n, std::uint32_t lshift) {
  std::uint64_t sub_borrow = 0;
  std::uint64_t mul_carry = 0;
  for (std::uint_fast32_t i = 0; i < n; ++i) {
    unsigned __int128 prod = factor;
    const std::uint64_t v =
        lshift ? (mul_buf[i] << lshift) +
                     (i > 0 ? mul_buf[i - 1] >> (64 - lshift) : 0)
               : mul_buf[i];
    prod *= v;
    prod += mul_carry;
    mul_carry = prod >> 64;
    std::uint64_t& c = cbuf[(cbuf_start + i) % (n + 1)];
    sub_with_borrow(c, prod & BI_WORD_MAX, sub_borrow, c);
  }
  std::uint64_t& c = cbuf[(cbuf_start + n) % (n + 1)];
  sub_with_borrow(c, mul_carry, sub_borrow, c);
  return sub_borrow;
}

/**
 * @brief Adds (val(add_buf) << lshift) to val(cbuf) (in place).
 *
 * Requirements:
 * 1. cbuf is a circular buffer of n + 1 words.
 * 2. the least significant word of val(cbuf) is at cbuf[cbuf_start].
 * 3. add_buf is a buffer of n words.
 * 4. val(cbuf) is a negative number in (2^64)s complement.
 * 5. abs(val(cbuf)) <= val(add_buf) << lshift.
 * 6. 0 <= lshift < 63
 * 7. (add_buf[n-1] << lshift) < 2^64
 */
void add_to_circular_buf(std::uint64_t* cbuf, std::uint_fast32_t cbuf_start,
                         const std::uint64_t* add_buf, std::uint32_t n,
                         std::uint32_t lshift) {
  std::uint64_t carry = 0;
  for (std::uint_fast32_t i = 0; i < n; ++i) {
    std::uint64_t& c = cbuf[(cbuf_start + i) % (n + 1)];
    const std::uint64_t v =
        lshift ? (add_buf[i] << lshift) +
                     (i > 0 ? add_buf[i - 1] >> (64 - lshift) : 0)
               : add_buf[i];
    add_with_carry(c, v, carry, c);
  }
  std::uint64_t& c = cbuf[(cbuf_start + n) % (n + 1)];
  add_with_carry(c, 0, carry, c);
  assert(carry);
}

/** Computes the number of bits `msw` must be shifted left so that its
 * new value is between 2^63 and 2^64. */
std::uint64_t compute_shift(std::uint64_t msw) {
  std::uint64_t shift = 0;
  if (!(msw & 0xffffffff00000000ull)) {
    shift += 32;
    msw <<= 32;
  }
  if (!(msw & 0xffff000000000000ull)) {
    shift += 16;
    msw <<= 16;
  }
  if (!(msw & 0xff00000000000000ull)) {
    shift += 8;
    msw <<= 8;
  }
  if (!(msw & 0xf000000000000000ull)) {
    shift += 4;
    msw <<= 4;
  }
  if (!(msw & 0xc000000000000000ull)) {
    shift += 2;
    msw <<= 2;
  }
  if (!(msw & 0x8000000000000000ull)) {
    shift += 1;
    msw <<= 1;
  }
  assert(msw >= (1ull << 63));
  assert(shift <= 63);
  return shift;
}

/**
 * @brief Computes an estimate of val(r) / (val(v) << lshift).
 *
 * The estimate uses the 3 leading words of val(r) and the 2 leading
 * words of (val(v) << lshift).
 *
 * Let d = (val(v) << lshift) and u be r rotated so that r_start is
 * the zero index. The initial estimate is (qhat,rhat) = divmod((u[n]<<64)
 * + u[n-1], d[n-1]). If qhat == 2^64 or qhat * d[n-2] > ((rhat << 64) +
 * u[n-2]), subtract 1 from qhat and add d[n-1] to rhat, and repeat this
 * check if rhat < 2^64. Finally, return qhat.
 *
 * When the requirements below hold, this estimate is either the
 * actual quotient or else one more than the actual quotient. See
 * the discussion around Algorithm D in Knuth.
 *
 * Requirements:
 * 1. r is a circular buffer of n + 1 words.
 * 2. The least significant word of r is at r[r_start].
 * 3. v is a buffer of n words.
 * 4. 2^63 <= (v[n-1] << lshift) < 2^64.
 * 5. n >= 2.
 * 6. val(r) / (val(v) << lshift) < 2^64.
 */
std::uint64_t estimate_quotient(const std::uint64_t* r,
                                std::uint_fast32_t r_start,
                                const std::uint64_t* v, std::uint32_t n,
                                std::uint64_t lshift) {
  static const unsigned __int128 BASE = static_cast<unsigned __int128>(1) << 64;
  // We make use of the lead 3 digits of the dividend and the lead 2 digits of
  // the divisor.
  const auto u1 = r[(r_start + n) % (n + 1)];
  const auto u2 = r[(r_start + n - 1) % (n + 1)];
  const auto u3 = r[(r_start + n - 2) % (n + 1)];
  const auto v1 =
      lshift ? (v[n - 1] << lshift) + (v[n - 2] >> (64 - lshift)) : v[n - 1];
  const auto v2 = lshift ? (v[n - 2] << lshift) +
                               ((n > 2) ? (v[n - 3] >> (64 - lshift)) : 0)
                         : v[n - 2];
  unsigned __int128 qhat = u1;
  qhat <<= 64;
  qhat += u2;
  unsigned __int128 rhat = qhat % v1;
  qhat /= v1;
  do {
    if (qhat == BASE || (qhat * v2) > (BASE * rhat + u3)) {
      --qhat;
      rhat += v1;
    } else {
      break;
    }
  } while (rhat < BASE);
  return qhat;
}

/**
 * @brief Divide two multiprecision numbers.
 *
 * This is based on Knuth's Algorithm D from section 4.3.1 of Volume
 * 2 of the Art of Computer Programming, but modified to use a separate
 * remainder buffer to avoid having to modify the dividend.
 *
 * Preconditions:
 * 1. abs(u_size) >= abs(v_size)
 * 2. abs(v_size) > 1
 * 3. q is a buffer of size 1 + abs(u_size) - abs(v_size)
 * 4. r is a buffer of size 1 + abs(v_size)
 *
 * Returns the sizes of q and r with the appropriate sign.
 */
std::pair<std::int32_t, std::int32_t> divide_bufs(
    const std::uint64_t* u, std::int32_t u_size, const std::uint64_t* v,
    std::int32_t v_size, std::uint64_t* q, std::uint64_t* r) {
  std::int32_t qsign = (u_size > 0) == (v_size > 0) ? 1 : -1;
  std::int32_t rsign = (u_size > 0) ? 1 : -1;
  const auto n = uabs(v_size);
  const auto m = uabs(u_size) - n;
  // D1. The first word of the divisor must be at least 1<<63 to
  // ensure the accuracy of our guess at quotients; if it isn't, we
  // shift both dividend and divisor to the left. Contrary to the
  // algorithm presented in the text, we perform these shifts "on the
  // fly" instead of modifying u and v initially.
  const auto lshift = compute_shift(v[n - 1]);
  const auto rshift = 64 - lshift;

  // The remainder buffer is a circular buffer containing the n+1
  // words of the current part of the dividend we care about. An
  // example using base-10 long division with 1-digit words:
  // *this = {2, 4, 1, 3} (3142)
  // divisor = {3, 5} (53).
  //
  // 1. rem = {1, 3, 0}, with start index at 0. 53 doesn't divide 31,
  //    so the first digit of the quotient is 0 and rem is still {1,
  //    3, 0}.
  //
  // 2. rem = {1, 3, 4}, with start index at 2. 53 divides 314 5 times
  //    with a remainder of 49, so the second digit of the quotient is
  //    5 and now rem = {4, 0, 9}.
  //
  // 3. rem = {4, 2, 9} with a start index at 1. 53 divides 492 9
  //    times with a remainder of 15, so the third digit of the quotient
  //    is 9 and now rem = {0, 5, 1}.
  //
  // 4. We've run out of digits, so we rotate rem to {5, 1, 0} and
  //    return it as the remainder.

  // Initially, the most significant word of r is < 2^63 and the most
  // significant word of the divisor is at least 2^63, so the quotient
  // is less than 2^64 (r is one word longer than the divisor).
  // Afterward, r is the remainder from the previous step of division
  // (which is less than the divisor) multiplied by 2^64 and added to
  // the next word of the dividend, so dividing by the divisor is
  // again less than 2^64 (hooray, induction!).
  if (lshift) {
    r[n] = u[m + n - 1] >> rshift;
    for (std::uint_fast32_t i = 1; i < n; ++i) {
      r[n - i] = (u[m + n - i] << lshift) + (u[m + n - i - 1] >> rshift);
    }
  } else {
    r[n] = 0;
    std::memcpy(r + 1, u + m + 1, (n - 1) * 8ull);
  }

  for (std::uint_fast32_t j = m + 1, r_start = 0; j > 0;
       --j, r_start = (r_start + n) % (n + 1)) {
    // copy the next digit of the dividend into r
    if (lshift) {
      r[r_start] = (u[j - 1] << lshift) + ((j > 1) ? (u[j - 2] >> rshift) : 0);
    } else {
      r[r_start] = u[j - 1];
    }

    // D3. Calculate qhat, our estimate of the next word of the
    // quotient. This estimate is almost always equal to the actual
    // word, but in rare cases it may be one more than the actual
    // word.
    const auto qhat = estimate_quotient(r, r_start, v, n, lshift);

    // D4. r <- r - qhat * v
    const bool underflow =
        subtract_product_from_circular_buf(r, r_start, qhat, v, n, lshift);
    if (underflow) {
      // D6. Adjust because qhat was an overestimate.
      add_to_circular_buf(r, r_start, v, n, lshift);
    }
    q[j - 1] = qhat - underflow;
  }
  const auto final_r_start =
      static_cast<std::uint64_t>((m / (n + 1) + 1)) * (n + 1) - m;
  std::rotate(r, r + final_r_start, r + n + 1);
  if (lshift) {
    // undo the shift in the remainder
    for (std::uint_fast32_t i = 0; i < n; ++i) {
      r[i] = (r[i] >> lshift) + (r[i + 1] << rshift);
    }
    assert(r[n] < (1ull << lshift));
  } else {
    assert(r[n] == 0);
  }
  std::int32_t rlen = n;
  while (rlen > 0 && !r[rlen - 1]) --rlen;
  return std::make_pair(qsign * (m + (q[m] != 0)), rsign * rlen);
}

}  // namespace

std::pair<managed_ptr<bigint>, managed_ptr<bigint>> bigint::divmod(
    const bigint& divisor) const {
  const auto n = uabs(divisor.size_);
  if (n == 0) {
    throw std::domain_error("Division by zero.");
  }
  const auto mplusn = uabs(size_);
  const auto hold = ctx().mgr->acquire_hold();

  if (mplusn < n || (mplusn == n && compare_magnitudes(*this, divisor) < 0)) {
    return std::make_pair(make_managed<bigint>(), make_managed<bigint>(*this));
  }
  const std::uint32_t m = mplusn - n;
  const bool quot_is_positive = (size_ > 0) == (divisor.size_ > 0);
  const bool rem_is_positive = size_ > 0;
  // handle a one-word divisor specially.
  if (n == 1) {
    if (m == 0) {
      // The quotient is certainly one word.
      return std::make_pair(
          make_managed<bigint>(s_.value / divisor.s_.value, quot_is_positive),
          make_managed<bigint>(s_.value % divisor.s_.value, rem_is_positive));
    } else if (m == 1) {
      // The quotient is one or two words.
      unsigned __int128 dividend = s_.data[1];
      dividend <<= 64;
      dividend += s_.data[0];
      unsigned __int128 div = divisor.s_.value;
      unsigned __int128 q = dividend / div;
      auto rem = make_managed<bigint>(dividend % div, rem_is_positive);
      if (q <= BI_WORD_MAX) {
        return std::make_pair(make_managed<bigint>(q, quot_is_positive),
                              std::move(rem));
      } else {
        return std::make_pair(
            make_managed<bigint>(q >> 64, q & BI_WORD_MAX, quot_is_positive),
            std::move(rem));
      }
    }
    // The quotient is certainly at least two words and the remainder
    // is one word.
    auto pbuf = ctx().mgr->allocate_private_buffer((m + 1) * 8ull);
    auto* quot = reinterpret_cast<std::uint64_t*>(pbuf.buf());
    unsigned __int128 d = 0;
    for (std::uint_fast32_t j = m + 1; j > 0; --j) {
      d <<= 64;
      d += s_.data[j - 1];
      quot[j - 1] = d / divisor.s_.value;
      d = d % divisor.s_.value;
    }
    const std::int32_t qlen = m + (quot[m] != 0);
    return std::make_pair(make_managed<bigint>(token(), std::move(pbuf),
                                               quot_is_positive ? qlen : -qlen),
                          make_managed<bigint>(d, rem_is_positive));
  }

  // The remainder may be multiple words.
  auto rembuf = ctx().mgr->allocate_private_buffer((n + 1) * 8ull);
  auto* rem = reinterpret_cast<std::uint64_t*>(rembuf.buf());

  std::pair<std::int32_t, std::int32_t> sizes;
  managed_ptr<bigint> quot;

  if (m == 0) {
    // The quotient is one word.
    std::uint64_t quotbuf;
    sizes = divide_bufs(s_.data, size_, divisor.s_.data, divisor.size_,
                        &quotbuf, rem);
    assert(uabs(sizes.first) <= 1);
    quot = make_managed<bigint>(quotbuf, quot_is_positive);
  } else if (m == 1) {
    // The quotient is one or two words.
    std::uint64_t quotbuf[2];
    sizes = divide_bufs(s_.data, size_, divisor.s_.data, divisor.size_, quotbuf,
                        rem);
    if (uabs(sizes.first) <= 1) {
      quot = make_managed<bigint>(quotbuf[0], quot_is_positive);
    } else {
      assert(uabs(sizes.first) == 2);
      quot = make_managed<bigint>(quotbuf[1], quotbuf[0], quot_is_positive);
    }
  } else {
    // The quotient is at least two words.
    auto quotpbuf = ctx().mgr->allocate_private_buffer((m + 1) * 8ull);
    auto* quotbuf = reinterpret_cast<std::uint64_t*>(quotpbuf.buf());
    sizes = divide_bufs(s_.data, size_, divisor.s_.data, divisor.size_, quotbuf,
                        rem);
    assert(uabs(sizes.first) > 1);
    quot = make_managed<bigint>(token(), std::move(quotpbuf), sizes.first);
  }
  // The remainder might always be as small as one word.
  if (uabs(sizes.second) <= 1) {
    return std::make_pair(std::move(quot),
                          make_managed<bigint>(rem[0], rem_is_positive));
  } else {
    return std::make_pair(
        std::move(quot),
        make_managed<bigint>(token(), std::move(rembuf), sizes.second));
  }
}

void bigint::free_buffer() {
  if (capacity_) {
    ctx().mgr->free_private_buffer(s_.data, capacity_);
  }
}

// NOLINTNEXTLINE(runtime/int)
static_assert(sizeof(unsigned long long) == sizeof(std::uint64_t));

void add_with_carry(std::uint64_t l, std::uint64_t r, std::uint64_t& carry,
                    std::uint64_t& result) {
  assert(carry == 0 || carry == 1);
  // This is toolchain-specific but __has_builtin(__builtin_addcll) doesn't
  // appear to work properly. Since I'm really only developing on a single
  // platform at the moment, I'll just use this for now.
  result = __builtin_addcll(l, r, carry, &carry);
}

void sub_with_borrow(std::uint64_t l, std::uint64_t r, std::uint64_t& borrow,
                     std::uint64_t& result) {
  assert(borrow == 0 || borrow == 1);
  result = __builtin_subcll(l, r, borrow, &borrow);
}

}  // namespace emil
