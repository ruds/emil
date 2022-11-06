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

#include <cassert>
#include <compare>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <limits>
#include <sstream>
#include <stdexcept>
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

}  // namespace

bigint::bigint() noexcept : s_{.value = 0}, size_(0), capacity_(0) {}

bigint::~bigint() { free_buffer(); }

namespace {

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

bigint::bigint(std::int64_t value) noexcept
    : s_{.value = uabs(value)}, size_(bigint_size(value)), capacity_(0) {}

bigint::bigint(std::uint64_t value, bool is_positive) noexcept
    : s_{.value = value},
      size_(value ? is_positive ? 1 : -1 : 0),
      capacity_(0) {}

bigint::bigint(token, PrivateBuffer buf, std::int32_t size) noexcept
    : size_(size), capacity_(buf.size() / 8) {
  assert(buf.size() % 8 == 0);
  s_.data = reinterpret_cast<std::uint64_t*>(buf.release());
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
      if (ld != rd) return l.size_ > 0 ? ld <=> rd : rd <=> ld;
    }
    return std::strong_ordering::equal;
  }
  assert(!r.capacity_);
  return l.s_.value <=> r.s_.value;
}

std::strong_ordering operator<=>(const bigint& l, const bigint& r) noexcept {
  if (l.size_ != r.size_) return l.size_ <=> r.size_;
  return bigint::compare_magnitudes(l, r);
}

std::strong_ordering operator<=>(std::int64_t l, const bigint& r) noexcept {
  return bigint(l) <=> r;
}

std::strong_ordering operator<=>(const bigint& l, std::int64_t r) noexcept {
  return l <=> bigint(r);
}

std::string bigint::to_string() const {
  if (!size_) return "0";
  std::ostringstream os;
  if (size_ < 0) os << "-";
  os << std::hex;
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

std::ostream& operator<<(std::ostream& os, const bigint& b) {
  return os << b.to_string();
}

std::ostream& operator<<(std::ostream& os, const managed_ptr<bigint>& b) {
  return os << b->to_string();
}

namespace {

// Add two bigints together
std::pair<PrivateBuffer, std::uint32_t> add_bufs(const std::uint64_t* l,
                                                 std::uint32_t ln,
                                                 const std::uint64_t* r,
                                                 std::uint32_t rn) {
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
    unsigned __int128 s = r[rn - 1] + l[ln - 1];
    if (s >= BI_WORD_MAX) ++capacity;
  }
  auto buf = ctx().mgr->allocate_private_buffer(capacity * 8);
  std::uint64_t* out = reinterpret_cast<std::uint64_t*>(buf.buf());
  std::uint64_t carry = 0;
  std::uint32_t len = 0;
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
    std::memcpy(out, l, n * 8);
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
    std::memcpy(out, r, n * 8);
    out += n;
    len += n;
  }
  if (carry) {
    *out = 1;
    ++len;
  }
  assert(len == capacity || len + 1 == capacity);
  return std::make_pair(std::move(buf), len);
}

// Subtract r from l, where r < l.
std::pair<PrivateBuffer, std::uint32_t> sub_bufs(const std::uint64_t* l,
                                                 std::uint32_t ln,
                                                 const std::uint64_t* r,
                                                 std::uint32_t rn) {
  assert(rn <= ln);
  const auto* lend = l + ln;
  const auto* rend = r + rn;
  auto buf = ctx().mgr->allocate_private_buffer(ln * 8);
  std::uint64_t* out = reinterpret_cast<std::uint64_t*>(buf.buf());
  std::uint64_t borrow = 0;
  std::uint32_t len = 0;
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
  std::memcpy(out, l, n * 8);
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
  std::uint64_t sum;
  std::uint64_t carry = 0;
  add_with_carry(l.s_.value, r.s_.value, carry, sum);
  if (carry) {
    auto hold = ctx().mgr->acquire_hold();
    auto buf = ctx().mgr->allocate_private_buffer(16);
    auto* data = reinterpret_cast<std::uint64_t*>(buf.buf());
    data[0] = sum;
    data[1] = 1;
    return make_managed<bigint>(bigint::new_token(), std::move(buf),
                                is_positive ? 2 : -2);
  } else {
    return make_managed<bigint>(sum, is_positive);
  }
}

managed_ptr<bigint> bigint::subtract_magnitudes(const bigint& l,
                                                const bigint& r,
                                                bool is_positive) {
  if (l.capacity_ || r.capacity_) {
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
  return make_managed<bigint>(l.s_.value - r.s_.value, is_positive);
}

managed_ptr<bigint> operator+(const bigint& l, const bigint& r) {
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

managed_ptr<bigint> operator*(const bigint& l, const bigint& r) {
  const auto m = uabs(l.size_);
  const auto n = uabs(r.size_);
  const std::int32_t sign = (l.size_ >= 0) == (r.size_ >= 0) ? 1 : -1;
  if (m == 0 || n == 0) return make_managed<bigint>();
  if (m <= 1 && n <= 1) {
    unsigned __int128 p = l.s_.value;
    p *= r.s_.value;
    if (p > BI_WORD_MAX) {
      auto hold = ctx().mgr->acquire_hold();
      auto pbuf = ctx().mgr->allocate_private_buffer(16);
      auto* d = reinterpret_cast<std::uint64_t*>(pbuf.buf());
      d[0] = p & BI_WORD_MAX;
      d[1] = p >> 64;
      return make_managed<bigint>(bigint::new_token(), std::move(pbuf),
                                  sign * 2);
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
  auto pbuf = ctx().mgr->allocate_private_buffer(plen * 8);
  auto* w = reinterpret_cast<std::uint64_t*>(pbuf.buf());
  const std::uint64_t* const u = l.ptr();
  const std::uint64_t* const v = r.ptr();
  // This is based on Knuth's Algorithm M from section 4.3.1 of Volume
  // 2 of the Art of Computer Programming.
  std::memset(w, 0, m * 8);
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
