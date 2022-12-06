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

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <tuple>

#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "testing/test_util.h"

namespace emil::testing {

class BigintTestAccessor {
 public:
  static std::int32_t size(const bigint& b) { return b.size_; }

  static std::uint32_t capacity(const bigint& b) { return b.capacity_; }
};

TEST(CarryOpsTest, AddWithCarry) {
  std::uint64_t carry = 0;
  std::uint64_t result = 0;
  add_with_carry(1ull << 63, 1ull << 63, carry, result);
  EXPECT_EQ(carry, 1);
  EXPECT_EQ(result, 0);

  add_with_carry(1ull << 63, 1ull << 63, carry, result);
  EXPECT_EQ(carry, 1);
  EXPECT_EQ(result, 1);

  add_with_carry(1ull << 62, 1ull << 63, carry, result);
  EXPECT_EQ(carry, 0);
  EXPECT_EQ(result, 0xc000000000000001ull);
}

TEST(CarryOpsTest, SubWithBorrow) {
  std::uint64_t borrow = 0;
  std::uint64_t result = 0;
  sub_with_borrow(1ull << 63, 1ull << 63, borrow, result);
  EXPECT_EQ(borrow, 0);
  EXPECT_EQ(result, 0);

  sub_with_borrow((1ull << 63) - 1, 1ull << 63, borrow, result);
  EXPECT_EQ(borrow, 1);
  EXPECT_EQ(result, 0xffffffffffffffffull);

  sub_with_borrow(1, 1, borrow, result);
  EXPECT_EQ(borrow, 1);
  EXPECT_EQ(result, 0xffffffffffffffffull);

  sub_with_borrow(10, 2, borrow, result);
  EXPECT_EQ(borrow, 0);
  EXPECT_EQ(result, 7);
}

TEST(BigintTest, Zeros) {
  TestContext tc;
  auto b1 = tc.root.add_root(make_managed<bigint>());
  auto b2 = tc.root.add_root(make_managed<bigint>(0));
  auto b3 = tc.root.add_root(make_managed<bigint>(0, true));
  auto b4 = tc.root.add_root(make_managed<bigint>(0, false));
  EXPECT_EQ(*b1, *b1);
  EXPECT_EQ(*b1, *b2);
  EXPECT_EQ(*b1, *b3);
  EXPECT_EQ(*b1, *b4);
  EXPECT_EQ(*b1, 0);
  EXPECT_EQ(b1->to_string(), "0");

  EXPECT_EQ(*b2, *b1);
  EXPECT_EQ(*b2, *b2);
  EXPECT_EQ(*b2, *b3);
  EXPECT_EQ(*b2, *b4);
  EXPECT_EQ(*b2, 0);
  EXPECT_EQ(b2->to_string(), "0");

  EXPECT_EQ(*b3, *b1);
  EXPECT_EQ(*b3, *b2);
  EXPECT_EQ(*b3, *b3);
  EXPECT_EQ(*b3, *b4);
  EXPECT_EQ(*b3, 0);
  EXPECT_EQ(b3->to_string(), "0");

  EXPECT_EQ(*b4, *b1);
  EXPECT_EQ(*b4, *b2);
  EXPECT_EQ(*b4, *b3);
  EXPECT_EQ(*b4, *b4);
  EXPECT_EQ(*b4, 0);
  EXPECT_EQ(b4->to_string(), "0");

  EXPECT_EQ(0, *b1);
  EXPECT_EQ(0, *b2);
  EXPECT_EQ(0, *b3);
  EXPECT_EQ(0, *b4);

  EXPECT_EQ(BigintTestAccessor::size(*b1), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b1), 0);
  EXPECT_EQ(BigintTestAccessor::size(*b2), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b2), 0);
  EXPECT_EQ(BigintTestAccessor::size(*b3), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b3), 0);
  EXPECT_EQ(BigintTestAccessor::size(*b4), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b4), 0);
}

TEST(BigintTest, Comparisons) {
  TestContext tc;
  auto zero = tc.root.add_root(make_managed<bigint>());
  auto tinypos = tc.root.add_root(make_managed<bigint>(105));
  auto tinyneg = tc.root.add_root(make_managed<bigint>(-105));
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 63, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 63, false));
  auto bigpos = tc.root.add_root(*smallpos + *smallpos);
  auto bigneg = tc.root.add_root(*smallneg + *smallneg);

  EXPECT_EQ(*zero, *zero);
  EXPECT_NE(*zero, *tinypos);
  EXPECT_NE(*zero, *tinyneg);
  EXPECT_NE(*zero, *smallpos);
  EXPECT_NE(*zero, *smallneg);
  EXPECT_NE(*zero, *bigpos);
  EXPECT_NE(*zero, *bigneg);
  EXPECT_FALSE(*zero < *zero);
  EXPECT_FALSE(*zero > *zero);
  EXPECT_LT(*zero, *smallpos);
  EXPECT_GT(*zero, *smallneg);
  EXPECT_LT(*zero, *bigpos);
  EXPECT_GT(*zero, *bigneg);

  EXPECT_NE(*tinypos, *zero);
  EXPECT_EQ(*tinypos, *tinypos);
  EXPECT_NE(*tinypos, *tinyneg);
  EXPECT_NE(*tinypos, *smallpos);
  EXPECT_NE(*tinypos, *smallneg);
  EXPECT_NE(*tinypos, *bigpos);
  EXPECT_NE(*tinypos, *bigneg);
  EXPECT_FALSE(*tinypos < *tinypos);
  EXPECT_FALSE(*tinypos > *tinypos);
  EXPECT_GT(*tinypos, *zero);
  EXPECT_GT(*tinypos, *tinyneg);
  EXPECT_LT(*tinypos, *smallpos);
  EXPECT_GT(*tinypos, *smallneg);
  EXPECT_LT(*tinypos, *bigpos);
  EXPECT_GT(*tinypos, *bigneg);

  EXPECT_NE(*tinyneg, *zero);
  EXPECT_NE(*tinyneg, *tinypos);
  EXPECT_EQ(*tinyneg, *tinyneg);
  EXPECT_NE(*tinyneg, *smallpos);
  EXPECT_NE(*tinyneg, *smallneg);
  EXPECT_NE(*tinyneg, *bigpos);
  EXPECT_NE(*tinyneg, *bigneg);
  EXPECT_FALSE(*tinyneg < *tinyneg);
  EXPECT_FALSE(*tinyneg > *tinyneg);
  EXPECT_LT(*tinyneg, *zero);
  EXPECT_LT(*tinyneg, *tinypos);
  EXPECT_LT(*tinyneg, *smallpos);
  EXPECT_GT(*tinyneg, *smallneg);
  EXPECT_LT(*tinyneg, *bigpos);
  EXPECT_GT(*tinyneg, *bigneg);

  EXPECT_NE(*smallpos, *zero);
  EXPECT_NE(*smallpos, *tinypos);
  EXPECT_NE(*smallpos, *tinyneg);
  EXPECT_EQ(*smallpos, *smallpos);
  EXPECT_NE(*smallpos, *smallneg);
  EXPECT_NE(*smallpos, *bigpos);
  EXPECT_NE(*smallpos, *bigneg);
  EXPECT_FALSE(*smallpos < *smallpos);
  EXPECT_FALSE(*smallpos > *smallpos);
  EXPECT_GT(*smallpos, *zero);
  EXPECT_GT(*smallpos, *tinypos);
  EXPECT_GT(*smallpos, *tinyneg);
  EXPECT_GT(*smallpos, *smallneg);
  EXPECT_LT(*smallpos, *bigpos);
  EXPECT_GT(*smallpos, *bigneg);

  EXPECT_NE(*bigpos, *zero);
  EXPECT_NE(*bigpos, *tinypos);
  EXPECT_NE(*bigpos, *tinyneg);
  EXPECT_NE(*bigpos, *smallpos);
  EXPECT_NE(*bigpos, *smallneg);
  EXPECT_EQ(*bigpos, *bigpos);
  EXPECT_NE(*bigpos, *bigneg);
  EXPECT_FALSE(*bigpos < *bigpos);
  EXPECT_FALSE(*bigpos > *bigpos);
  EXPECT_GT(*bigpos, *zero);
  EXPECT_GT(*bigpos, *tinypos);
  EXPECT_GT(*bigpos, *tinyneg);
  EXPECT_GT(*bigpos, *smallneg);
  EXPECT_GT(*bigpos, *smallpos);
  EXPECT_GT(*bigpos, *bigneg);

  EXPECT_NE(*smallneg, *zero);
  EXPECT_NE(*smallneg, *tinypos);
  EXPECT_NE(*smallneg, *tinyneg);
  EXPECT_NE(*smallneg, *smallpos);
  EXPECT_EQ(*smallneg, *smallneg);
  EXPECT_NE(*smallneg, *bigpos);
  EXPECT_NE(*smallneg, *bigneg);
  EXPECT_FALSE(*smallneg < *smallneg);
  EXPECT_FALSE(*smallneg > *smallneg);
  EXPECT_LT(*smallneg, *zero);
  EXPECT_LT(*smallneg, *tinypos);
  EXPECT_LT(*smallneg, *tinyneg);
  EXPECT_LT(*smallneg, *smallpos);
  EXPECT_LT(*smallneg, *bigpos);
  EXPECT_GT(*smallneg, *bigneg);

  EXPECT_NE(*bigneg, *zero);
  EXPECT_NE(*bigneg, *tinypos);
  EXPECT_NE(*bigneg, *tinyneg);
  EXPECT_NE(*bigneg, *smallpos);
  EXPECT_NE(*bigneg, *smallneg);
  EXPECT_NE(*bigneg, *bigpos);
  EXPECT_EQ(*bigneg, *bigneg);
  EXPECT_FALSE(*bigneg < *bigneg);
  EXPECT_FALSE(*bigneg > *bigneg);
  EXPECT_LT(*bigneg, *zero);
  EXPECT_LT(*bigneg, *tinypos);
  EXPECT_LT(*bigneg, *tinyneg);
  EXPECT_LT(*bigneg, *smallneg);
  EXPECT_LT(*bigneg, *smallpos);
  EXPECT_LT(*bigneg, *bigpos);

  EXPECT_EQ(BigintTestAccessor::size(*zero), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*zero), 0);
  EXPECT_EQ(BigintTestAccessor::size(*tinypos), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*tinypos), 0);
  EXPECT_EQ(BigintTestAccessor::size(*tinyneg), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*tinyneg), 0);
  EXPECT_EQ(BigintTestAccessor::size(*smallpos), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*smallpos), 0);
  EXPECT_EQ(BigintTestAccessor::size(*bigpos), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*bigpos), 2);
  EXPECT_EQ(BigintTestAccessor::size(*smallneg), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*smallneg), 0);
  EXPECT_EQ(BigintTestAccessor::size(*bigneg), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*bigneg), 2);
}

TEST(BigintTest, Addition) {
  TestContext tc;
  auto zero = tc.root.add_root(make_managed<bigint>());
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 63, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 63, false));
  auto bigpos = tc.root.add_root(*smallpos + *smallpos);
  auto bigneg = tc.root.add_root(*smallneg + *smallneg);

  EXPECT_EQ(zero->to_string(), "0");
  EXPECT_EQ(smallpos->to_string(), "8000000000000000");
  EXPECT_EQ(smallneg->to_string(), "-8000000000000000");
  EXPECT_EQ(bigpos->to_string(), "10000000000000000");
  EXPECT_EQ(bigneg->to_string(), "-10000000000000000");

  // adding zero
  auto sum = tc.root.add_root(*zero + *zero);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero + 0);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 + *zero);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero + *smallpos);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + *zero);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 + *smallpos);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + 0);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero + *smallneg);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + *zero);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 + *smallneg);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + 0);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero + *bigpos);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos + *zero);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 0 + *bigpos);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos + 0);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *zero + *bigneg);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg + *zero);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 0 + *bigneg);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg + 0);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  // adding a small positive number
  sum = tc.root.replace_root(sum, *smallpos + *smallpos);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 42 + *smallpos);
  EXPECT_EQ(sum->to_string(), "800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + 42);
  EXPECT_EQ(sum->to_string(), "800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + *smallneg);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + *smallpos);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 42 + *smallneg);
  EXPECT_EQ(sum->to_string(), "-7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + 42);
  EXPECT_EQ(sum->to_string(), "-7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + *bigpos);
  EXPECT_EQ(sum->to_string(), "18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos + *smallpos);
  EXPECT_EQ(sum->to_string(), "18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 42 + *bigpos);
  EXPECT_EQ(sum->to_string(), "1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos + 42);
  EXPECT_EQ(sum->to_string(), "1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *smallpos + *bigneg);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg + *smallpos);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 42 + *bigneg);
  EXPECT_EQ(sum->to_string(), "-FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg + 42);
  EXPECT_EQ(sum->to_string(), "-FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  // adding a small negative number
  sum = tc.root.replace_root(sum, *smallneg + *smallneg);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *smallneg + -42);
  EXPECT_EQ(sum->to_string(), "-800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 + *smallneg);
  EXPECT_EQ(sum->to_string(), "-800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 + *smallpos);
  EXPECT_EQ(sum->to_string(), "7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos + -42);
  EXPECT_EQ(sum->to_string(), "7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + *bigpos);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigpos + *smallneg);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 + *bigpos);
  EXPECT_EQ(sum->to_string(), "FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigpos + -42);
  EXPECT_EQ(sum->to_string(), "FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg + *bigneg);
  EXPECT_EQ(sum->to_string(), "-18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg + *smallneg);
  EXPECT_EQ(sum->to_string(), "-18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, -42 + *bigneg);
  EXPECT_EQ(sum->to_string(), "-1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg + -42);
  EXPECT_EQ(sum->to_string(), "-1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  // adding a large number
  sum = tc.root.replace_root(sum, *bigpos + *bigpos);
  EXPECT_EQ(sum->to_string(), "20000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos + *bigneg);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg + *bigpos);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg + *bigneg);
  EXPECT_EQ(sum->to_string(), "-20000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);
}

TEST(BigintTest, Subtraction) {
  TestContext tc;
  auto zero = tc.root.add_root(make_managed<bigint>());
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 63, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 63, false));
  auto bigpos = tc.root.add_root(*smallpos + *smallpos);
  auto bigneg = tc.root.add_root(*smallneg + *smallneg);

  EXPECT_EQ(zero->to_string(), "0");
  EXPECT_EQ(smallpos->to_string(), "8000000000000000");
  EXPECT_EQ(smallneg->to_string(), "-8000000000000000");
  EXPECT_EQ(bigpos->to_string(), "10000000000000000");
  EXPECT_EQ(bigneg->to_string(), "-10000000000000000");

  auto sum = tc.root.add_root(*zero - *zero);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero - 0);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 - *zero);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero - *smallneg);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - *zero);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 - *smallneg);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - 0);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero - *smallpos);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - *zero);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 0 - *smallpos);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - 0);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *zero - *bigneg);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - *zero);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 0 - *bigneg);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - 0);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *zero - *bigpos);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg - *zero);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 0 - *bigpos);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg - 0);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *smallpos - *smallneg);
  EXPECT_EQ(*sum, *bigpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 42 - *smallneg);
  EXPECT_EQ(sum->to_string(), "800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - -42);
  EXPECT_EQ(sum->to_string(), "800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - *smallpos);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - *smallneg);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 42 - *smallpos);
  EXPECT_EQ(sum->to_string(), "-7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - -42);
  EXPECT_EQ(sum->to_string(), "-7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - *bigneg);
  EXPECT_EQ(sum->to_string(), "18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - *smallneg);
  EXPECT_EQ(sum->to_string(), "18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, 42 - *bigneg);
  EXPECT_EQ(sum->to_string(), "1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - -42);
  EXPECT_EQ(sum->to_string(), "1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *smallpos - *bigpos);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg - *smallneg);
  EXPECT_EQ(*sum, *smallneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, 42 - *bigpos);
  EXPECT_EQ(sum->to_string(), "-FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg - -42);
  EXPECT_EQ(sum->to_string(), "-FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - *smallpos);
  EXPECT_EQ(*sum, *bigneg);
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *smallneg - 42);
  EXPECT_EQ(sum->to_string(), "-800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 - *smallpos);
  EXPECT_EQ(sum->to_string(), "-800000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 - *smallneg);
  EXPECT_EQ(sum->to_string(), "7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallpos - 42);
  EXPECT_EQ(sum->to_string(), "7FFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - *bigneg);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigpos - *smallpos);
  EXPECT_EQ(*sum, *smallpos);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, -42 - *bigneg);
  EXPECT_EQ(sum->to_string(), "FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigpos - 42);
  EXPECT_EQ(sum->to_string(), "FFFFFFFFFFFFFFD6");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *smallneg - *bigpos);
  EXPECT_EQ(sum->to_string(), "-18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg - *smallpos);
  EXPECT_EQ(sum->to_string(), "-18000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, -42 - *bigpos);
  EXPECT_EQ(sum->to_string(), "-1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigneg - 42);
  EXPECT_EQ(sum->to_string(), "-1000000000000002A");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - *bigneg);
  EXPECT_EQ(sum->to_string(), "20000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);

  sum = tc.root.replace_root(sum, *bigpos - *bigpos);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg - *bigneg);
  EXPECT_EQ(*sum, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *bigneg - *bigpos);
  EXPECT_EQ(sum->to_string(), "-20000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*sum), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 2);
}

TEST(BigintTest, Multiplication) {
  TestContext tc;
  auto zero = tc.root.add_root(make_managed<bigint>());
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 61, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 61, false));
  auto bigpos = tc.root.add_root(*smallpos * 64);
  auto bigneg = tc.root.add_root(*smallneg * 64);

  EXPECT_EQ(zero->to_string(), "0");
  EXPECT_EQ(smallpos->to_string(), "2000000000000000");
  EXPECT_EQ(smallneg->to_string(), "-2000000000000000");
  EXPECT_EQ(bigpos->to_string(), "80000000000000000");
  EXPECT_EQ(bigneg->to_string(), "-80000000000000000");

  // multiplying by zero
  auto prod = tc.root.add_root(*zero + *zero);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *zero * *smallpos);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallpos * *zero);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *zero * *smallneg);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallneg * *zero);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *zero * *bigpos);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *bigpos * *zero);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *zero * *bigneg);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *bigneg * *zero);
  EXPECT_EQ(*prod, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*prod), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  // multiplying by a small positive number
  prod = tc.root.replace_root(prod, *smallpos * *smallpos);
  EXPECT_EQ(prod->to_string(), "4000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 2);

  prod = tc.root.replace_root(prod, 4 * *smallpos);
  EXPECT_EQ(prod->to_string(), "8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallpos * 4);
  EXPECT_EQ(prod->to_string(), "8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallpos * *smallneg);
  EXPECT_EQ(prod->to_string(), "-4000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 2);

  prod = tc.root.replace_root(prod, *smallneg * *smallpos);
  EXPECT_EQ(prod->to_string(), "-4000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 2);

  prod = tc.root.replace_root(prod, 4 * *smallneg);
  EXPECT_EQ(prod->to_string(), "-8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallneg * 4);
  EXPECT_EQ(prod->to_string(), "-8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallpos * *bigpos);
  EXPECT_EQ(prod->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, *bigpos * *smallpos);
  EXPECT_EQ(prod->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, 4 * *bigpos);
  EXPECT_EQ(prod->to_string(), "200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);

  prod = tc.root.replace_root(prod, *bigpos * 4);
  EXPECT_EQ(prod->to_string(), "200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);

  prod = tc.root.replace_root(prod, *smallpos * *bigneg);
  EXPECT_EQ(prod->to_string(), "-100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, *bigneg * *smallpos);
  EXPECT_EQ(prod->to_string(), "-100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, 4 * *bigneg);
  EXPECT_EQ(prod->to_string(), "-200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);

  prod = tc.root.replace_root(prod, *bigneg * 4);
  EXPECT_EQ(prod->to_string(), "-200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);

  // multiplying by a small negative number
  prod = tc.root.replace_root(prod, *smallneg * *smallneg);
  EXPECT_EQ(prod->to_string(), "4000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 2);

  prod = tc.root.replace_root(prod, *smallneg * -4);
  EXPECT_EQ(prod->to_string(), "8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, -4 * *smallneg);
  EXPECT_EQ(prod->to_string(), "8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, -4 * *smallpos);
  EXPECT_EQ(prod->to_string(), "-8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallpos * -4);
  EXPECT_EQ(prod->to_string(), "-8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 0);

  prod = tc.root.replace_root(prod, *smallneg * *bigpos);
  EXPECT_EQ(prod->to_string(), "-100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, *bigpos * *smallneg);
  EXPECT_EQ(prod->to_string(), "-100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, -4 * *bigpos);
  EXPECT_EQ(prod->to_string(), "-200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);

  prod = tc.root.replace_root(prod, *bigpos * -4);
  EXPECT_EQ(prod->to_string(), "-200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -2);

  prod = tc.root.replace_root(prod, *smallneg * *bigneg);
  EXPECT_EQ(prod->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, *bigneg * *smallneg);
  EXPECT_EQ(prod->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*prod), 3);

  prod = tc.root.replace_root(prod, -4 * *bigneg);
  EXPECT_EQ(prod->to_string(), "200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);

  prod = tc.root.replace_root(prod, *bigneg * -4);
  EXPECT_EQ(prod->to_string(), "200000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 2);

  // multiplying by a large number
  prod = tc.root.replace_root(prod, *bigpos * *bigpos);
  EXPECT_EQ(prod->to_string(), "4000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);

  prod = tc.root.replace_root(prod, *bigpos * *bigneg);
  EXPECT_EQ(prod->to_string(), "-4000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);

  prod = tc.root.replace_root(prod, *bigneg * *bigpos);
  EXPECT_EQ(prod->to_string(), "-4000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), -3);

  prod = tc.root.replace_root(prod, *bigneg * *bigneg);
  EXPECT_EQ(prod->to_string(), "4000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*prod), 3);
}

TEST(BigintTest, LeftShift) {
  TestContext tc;
  const auto zero = tc.root.add_root(make_managed<bigint>());
  const auto tinypos = tc.root.add_root(make_managed<bigint>(105));
  const auto tinyneg = tc.root.add_root(make_managed<bigint>(-105));
  const auto b = tc.root.add_root(make_managed<bigint>(1, 0, true));
  const auto bneg = tc.root.add_root(-*b);
  const auto a5 = tc.root.add_root(
      make_managed<bigint>(0xa5a5a5a5a5a5a5a5ull, 0x5a5a5a5a5a5a5a5aull, true));

  auto r = tc.root.add_root(*zero << 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *zero << 20);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *zero << (1u << 28));
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *b << 0);
  EXPECT_EQ(*r, *b);
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *tinypos << 12);
  EXPECT_EQ(*r, 430080);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinypos << 57);
  EXPECT_EQ(*r, bigint(15132094747964866560ull, true));
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinypos << 58);
  EXPECT_EQ(r->to_string(), "1A400000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *tinyneg << 12);
  EXPECT_EQ(*r, -430080);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinyneg << 57);
  EXPECT_EQ(*r, bigint(15132094747964866560ull, false));
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinyneg << 58);
  EXPECT_EQ(r->to_string(), "-1A400000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *b << 63);
  EXPECT_EQ(r->to_string(), "80000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *b << 64);
  EXPECT_EQ(r->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *b << 65);
  EXPECT_EQ(r->to_string(), "200000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *bneg << 0);
  EXPECT_EQ(*r, *bneg);
  EXPECT_EQ(BigintTestAccessor::size(*r), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *bneg << 63);
  EXPECT_EQ(r->to_string(), "-80000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *bneg << 64);
  EXPECT_EQ(r->to_string(), "-100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *bneg << 65);
  EXPECT_EQ(r->to_string(), "-200000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), -3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 0);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A55A5A5A5A5A5A5A5A");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 << 1);
  EXPECT_EQ(r->to_string(), "14B4B4B4B4B4B4B4AB4B4B4B4B4B4B4B4");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 2);
  EXPECT_EQ(r->to_string(), "296969696969696956969696969696968");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 3);
  EXPECT_EQ(r->to_string(), "52D2D2D2D2D2D2D2AD2D2D2D2D2D2D2D0");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 60);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A55A5A5A5A5A5A5A5A000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 61);
  EXPECT_EQ(r->to_string(), "14B4B4B4B4B4B4B4AB4B4B4B4B4B4B4B4000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 62);
  EXPECT_EQ(r->to_string(), "296969696969696956969696969696968000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 63);
  EXPECT_EQ(r->to_string(), "52D2D2D2D2D2D2D2AD2D2D2D2D2D2D2D0000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 64);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A55A5A5A5A5A5A5A5A0000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 3);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 3);

  r = tc.root.replace_root(r, *a5 << 65);
  EXPECT_EQ(r->to_string(),
            "14B4B4B4B4B4B4B4AB4B4B4B4B4B4B4B40000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 4);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 4);

  r = tc.root.replace_root(r, *a5 << 66);
  EXPECT_EQ(r->to_string(),
            "2969696969696969569696969696969680000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 4);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 4);

  r = tc.root.replace_root(r, *a5 << 67);
  EXPECT_EQ(r->to_string(),
            "52D2D2D2D2D2D2D2AD2D2D2D2D2D2D2D00000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 4);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 4);
}

TEST(BigintTest, RightShift) {
  TestContext tc;
  const auto zero = tc.root.add_root(make_managed<bigint>());
  const auto tinypos = tc.root.add_root(make_managed<bigint>(105));
  const auto tinyneg = tc.root.add_root(make_managed<bigint>(-105));
  const auto b = tc.root.add_root(make_managed<bigint>(1, 0, true));
  const auto bneg = tc.root.add_root(-*b);
  const auto a5 = tc.root.add_root(
      make_managed<bigint>(0xa5a5a5a5a5a5a5a5ull, 0x5a5a5a5a5a5a5a5aull, true));
  const auto a5_258 = tc.root.add_root(*a5 << 258);

  auto r = tc.root.add_root(*zero >> 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *zero >> 20);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *zero >> (1u << 28));
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *b >> 0);
  EXPECT_EQ(*r, *b);
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *b >> 1);
  EXPECT_EQ(r->to_string(), "8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *b >> 60);
  EXPECT_EQ(*r, 16);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *b >> 64);
  EXPECT_EQ(*r, 1);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *b >> 65);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *bneg >> 0);
  EXPECT_EQ(*r, *bneg);
  EXPECT_EQ(BigintTestAccessor::size(*r), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *bneg >> 1);
  EXPECT_EQ(r->to_string(), "-8000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *bneg >> 60);
  EXPECT_EQ(*r, -16);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *bneg >> 64);
  EXPECT_EQ(*r, -1);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *bneg >> 65);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinypos >> 5);
  EXPECT_EQ(*r, 3);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinypos >> 6);
  EXPECT_EQ(*r, 1);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinypos >> 7);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinyneg >> 5);
  EXPECT_EQ(*r, -3);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinyneg >> 6);
  EXPECT_EQ(*r, -1);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *tinyneg >> 7);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 0);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A55A5A5A5A5A5A5A5A");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 1);
  EXPECT_EQ(r->to_string(), "52D2D2D2D2D2D2D2AD2D2D2D2D2D2D2D");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 2);
  EXPECT_EQ(r->to_string(), "29696969696969695696969696969696");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 3);
  EXPECT_EQ(r->to_string(), "14B4B4B4B4B4B4B4AB4B4B4B4B4B4B4B");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 60);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A55");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 61);
  EXPECT_EQ(r->to_string(), "52D2D2D2D2D2D2D2A");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 62);
  EXPECT_EQ(r->to_string(), "29696969696969695");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 63);
  EXPECT_EQ(r->to_string(), "14B4B4B4B4B4B4B4A");
  EXPECT_EQ(BigintTestAccessor::size(*r), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 2);

  r = tc.root.replace_root(r, *a5 >> 64);
  EXPECT_EQ(r->to_string(), "A5A5A5A5A5A5A5A5");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 124);
  EXPECT_EQ(r->to_string(), "A");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 125);
  EXPECT_EQ(r->to_string(), "5");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 126);
  EXPECT_EQ(r->to_string(), "2");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 127);
  EXPECT_EQ(r->to_string(), "1");
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5 >> 128);
  EXPECT_EQ(r->to_string(), "0");
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  r = tc.root.replace_root(r, *a5_258 >> 128);
  EXPECT_EQ(
      r->to_string(),
      "29696969696969695696969696969696800000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 5);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 5);

  r = tc.root.replace_root(r, *a5_258 >> 130);
  EXPECT_EQ(r->to_string(),
            "A5A5A5A5A5A5A5A55A5A5A5A5A5A5A5A00000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::size(*r), 4);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 4);
}

// This test takes a long time to run.
TEST(BigintTest, DISABLED_Overflow) {
  TestContext tc;
  const auto max_bit = tc.root.add_root(bigint(1) << 0x1FFFFFFFBFull);
  const auto rest = tc.root.add_root(*max_bit - 1);
  const auto max_bigint = tc.root.add_root(*max_bit + *rest);

  auto sum = tc.root.add_root(*max_bigint - *max_bigint);
  EXPECT_EQ(*sum, 0);
  EXPECT_EQ(BigintTestAccessor::size(*sum), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*sum), 0);

  sum = tc.root.replace_root(sum, *max_bigint - 1);
  EXPECT_EQ(BigintTestAccessor::size(*sum),
            std::numeric_limits<std::int32_t>::max());

  EXPECT_THROW(auto t = *max_bigint + 1, std::overflow_error);
  EXPECT_THROW(auto t = *max_bit << 1, std::overflow_error);
  EXPECT_THROW(auto t = *max_bit * 2, std::overflow_error);
}

TEST(BigintTest, DivisionWithZeros) {
  TestContext tc;
  auto zero = tc.root.add_root(make_managed<bigint>());
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 61, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 61, false));
  auto bigpos = tc.root.add_root(*smallpos * 64);
  auto bigneg = tc.root.add_root(*smallneg * 64);

  EXPECT_THROW(zero->divmod(*zero), std::domain_error);
  EXPECT_THROW(smallpos->divmod(*zero), std::domain_error);
  EXPECT_THROW(bigpos->divmod(*zero), std::domain_error);
  EXPECT_THROW(smallneg->divmod(*zero), std::domain_error);
  EXPECT_THROW(bigneg->divmod(*zero), std::domain_error);

  auto [q, r] = zero->divmod(*smallpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = zero->divmod(*smallneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = zero->divmod(*bigpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = zero->divmod(*bigneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
}

TEST(BigintTest, DivisionWithSmallDividends) {
  TestContext tc;
  auto tinypos1 = tc.root.add_root(make_managed<bigint>(105));
  auto tinypos2 = tc.root.add_root(make_managed<bigint>(106));
  auto tinyneg1 = tc.root.add_root(make_managed<bigint>(-105));
  auto tinyneg2 = tc.root.add_root(make_managed<bigint>(-106));
  auto bigpos = tc.root.add_root(*tinypos1 * (1ll << 62));
  auto bigneg = tc.root.add_root(*tinyneg1 * (1ll << 62));

  // small positive dividend
  auto [q, r] = tinypos1->divmod(*tinypos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 1);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos1->divmod(*tinypos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 105);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos2->divmod(*tinypos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 1);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 1);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos1->divmod(*bigpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 105);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos1->divmod(*tinyneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -1);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos1->divmod(*tinyneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 105);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos2->divmod(*tinyneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -1);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 1);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinypos1->divmod(*bigneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 105);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  // small negative dividend
  std::tie(q, r) = tinyneg1->divmod(*tinypos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -1);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg1->divmod(*tinypos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -105);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg2->divmod(*tinypos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -1);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -1);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg1->divmod(*bigpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -105);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg1->divmod(*tinyneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 1);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg1->divmod(*tinyneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -105);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg2->divmod(*tinyneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 1);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -1);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = tinyneg1->divmod(*bigneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -105);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
}

// test case: 2-word dividend, 1-word divisor, 1-word quotient
TEST(BigintTest, Division_2Dividend_1Divisor_1Quotient) {
  TestContext tc;
  auto smallpos = tc.root.add_root(make_managed<bigint>(1ull << 63, true));
  auto smallneg = tc.root.add_root(make_managed<bigint>(1ull << 63, false));
  auto bigpos = tc.root.add_root(*smallpos * 42);
  auto bigpos2 = tc.root.add_root(*bigpos + 825);
  auto bigneg = tc.root.add_root(*smallneg * 42);
  auto bigneg2 = tc.root.add_root(*bigneg - 825);

  EXPECT_EQ(BigintTestAccessor::size(*smallpos), 1);
  EXPECT_EQ(BigintTestAccessor::size(*smallneg), -1);
  EXPECT_EQ(BigintTestAccessor::size(*bigpos), 2);
  EXPECT_EQ(BigintTestAccessor::size(*bigneg), -2);
  EXPECT_EQ(BigintTestAccessor::size(*bigpos2), 2);
  EXPECT_EQ(BigintTestAccessor::size(*bigneg2), -2);

  auto [q, r] = bigpos->divmod(*smallpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 42);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos->divmod(*smallneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -42);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos2->divmod(*smallpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 42);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 825);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos2->divmod(*smallneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -42);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 825);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg->divmod(*smallpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -42);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg->divmod(*smallneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 42);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg2->divmod(*smallpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, -42);
  EXPECT_EQ(BigintTestAccessor::size(*q), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -825);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg2->divmod(*smallneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, 42);
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, -825);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
}

// test case: 2-word dividend, 1-word divisor, 2-word quotient
TEST(BigintTest, Division_2Dividend_1Divisor_2Quotient) {
  TestContext tc;
  auto tinypos = tc.root.add_root(make_managed<bigint>(105));
  auto tinyneg = tc.root.add_root(make_managed<bigint>(-105));
  auto bigpos = tc.root.add_root(bigint(1ull << 63, true) * 425);
  auto bigpos2 = tc.root.add_root(*bigpos - 40);
  auto bigneg = tc.root.add_root(-*bigpos);
  auto bigneg2 = tc.root.add_root(*bigneg + 40);

  EXPECT_EQ(BigintTestAccessor::size(*tinypos), 1);
  EXPECT_EQ(BigintTestAccessor::size(*tinyneg), -1);
  EXPECT_EQ(BigintTestAccessor::size(*bigpos), 2);
  EXPECT_EQ(BigintTestAccessor::size(*bigpos2), 2);
  EXPECT_EQ(BigintTestAccessor::size(*bigneg), -2);
  EXPECT_EQ(BigintTestAccessor::size(*bigneg2), -2);

  auto [q, r] = bigpos->divmod(*tinypos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 40);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos->divmod(*tinyneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "-20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 40);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos2->divmod(*tinypos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigpos2->divmod(*tinyneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "-20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg->divmod(*tinypos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "-20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, -40);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg->divmod(*tinyneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, -40);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg2->divmod(*tinypos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "-20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), -2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = bigneg2->divmod(*tinyneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(q->to_string(), "20618618618618618");
  EXPECT_EQ(BigintTestAccessor::size(*q), 2);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 2);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
}

// test case: long dividend, 1-word divisor
TEST(BigintTest, Division_LongDividend_1Divisor) {
  TestContext tc;
  auto f1 = tc.root.add_root(
      make_managed<bigint>(0x00ffddddeeeeffffull, 0xfefedcdcbaba9898ull, true));
  auto quotpos = tc.root.add_root(*f1 * *f1);

  auto vpos1 = tc.root.add_root(make_managed<bigint>(0x1badd00dll));
  auto upos1 = tc.root.add_root(*quotpos * *vpos1);
  auto upos1r = tc.root.add_root(*upos1 + 100);

  auto vpos2 = tc.root.add_root(make_managed<bigint>(420));
  auto upos2 = tc.root.add_root(*quotpos * *vpos2);
  auto upos2r = tc.root.add_root(*upos2 + 100);

  EXPECT_EQ(BigintTestAccessor::size(*quotpos), 4);

  EXPECT_EQ(BigintTestAccessor::size(*vpos1), 1);
  EXPECT_EQ(BigintTestAccessor::size(*upos1), 5);
  EXPECT_EQ(BigintTestAccessor::size(*upos1r), 5);

  EXPECT_EQ(BigintTestAccessor::size(*vpos2), 1);
  EXPECT_EQ(BigintTestAccessor::size(*upos2), 4);
  EXPECT_EQ(BigintTestAccessor::size(*upos2r), 4);

  auto quotneg = tc.root.add_root(-*quotpos);
  auto vneg1 = tc.root.add_root(-*vpos1);
  auto uneg1 = tc.root.add_root(-*upos1);
  auto uneg1r = tc.root.add_root(-*upos1r);
  auto vneg2 = tc.root.add_root(-*vpos2);
  auto uneg2 = tc.root.add_root(-*upos2);
  auto uneg2r = tc.root.add_root(-*upos2r);

  auto [q, r] = upos1->divmod(*vpos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos1r->divmod(*vpos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 100);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos1->divmod(*vneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos1r->divmod(*vneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 100);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg1->divmod(*vneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg1r->divmod(*vneg1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, -100);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg1->divmod(*vpos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg1r->divmod(*vpos1);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, -100);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos2->divmod(*vpos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos2r->divmod(*vpos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 100);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos2->divmod(*vneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = upos2r->divmod(*vneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 100);
  EXPECT_EQ(BigintTestAccessor::size(*r), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg2->divmod(*vneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg2r->divmod(*vneg2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotpos);
  EXPECT_EQ(BigintTestAccessor::size(*q), 4);
  EXPECT_EQ(*r, -100);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg2->divmod(*vpos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = uneg2r->divmod(*vpos2);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *quotneg);
  EXPECT_EQ(BigintTestAccessor::size(*q), -4);
  EXPECT_EQ(*r, -100);
  EXPECT_EQ(BigintTestAccessor::size(*r), -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
}

// test case: divisor and dividend both at least two words, divisor
// large enough that no shifting is necessary (i.e. highest word is at
// least 2^63)
TEST(BigintTest, LongDivision_NoShift) {
  TestContext tc;
  const auto vpos = tc.root.add_root(
      make_managed<bigint>(0xd00db3c001a5a5a5ull, 0xc4f300fff4c4deffull, true));
  const auto vneg = tc.root.add_root(-*vpos);
  const auto zero = tc.root.add_root(make_managed<bigint>());
  const auto rspos = tc.root.add_root(make_managed<bigint>(4500000000ll));
  const auto rsneg = tc.root.add_root(-*rspos);
  const auto rlpos = tc.root.add_root(make_managed<bigint>(250, 1047, true));
  const auto rlneg = tc.root.add_root(-*rlpos);
  const auto q0pos = tc.root.add_root(make_managed<bigint>(1));
  const auto q0neg = tc.root.add_root(-*q0pos);
  const auto q1pos = tc.root.add_root(make_managed<bigint>(92576));
  const auto q1neg = tc.root.add_root(-*q1pos);
  const auto q2pos =
      tc.root.add_root(make_managed<bigint>(0xffffffffffffffffull, true));
  const auto q2neg = tc.root.add_root(-*q2pos);
  const auto q3pos = tc.root.add_root(make_managed<bigint>(1, 888888, true));
  const auto q3neg = tc.root.add_root(-*q3pos);
  const auto q4pos = tc.root.add_root(*q0pos << 127);
  const auto q4neg = tc.root.add_root(-*q4pos);
  const auto q5pos = tc.root.add_root(*q3pos << 128);
  const auto q5neg = tc.root.add_root(-*q5pos);
  const auto u0pos = tc.root.add_root(*q0pos * *vpos);
  const auto u0neg = tc.root.add_root(-*u0pos);
  const auto u0rspos = tc.root.add_root(*u0pos + *rspos);
  const auto u0rsneg = tc.root.add_root(-*u0rspos);
  const auto u0rlpos = tc.root.add_root(*u0pos + *rlpos);
  const auto u0rlneg = tc.root.add_root(-*u0rlpos);
  const auto u1pos = tc.root.add_root(*q1pos * *vpos);
  const auto u1neg = tc.root.add_root(-*u1pos);
  const auto u1rspos = tc.root.add_root(*u1pos + *rspos);
  const auto u1rsneg = tc.root.add_root(-*u1rspos);
  const auto u1rlpos = tc.root.add_root(*u1pos + *rlpos);
  const auto u1rlneg = tc.root.add_root(-*u1rlpos);
  const auto u2pos = tc.root.add_root(*q2pos * *vpos);
  const auto u2neg = tc.root.add_root(-*u2pos);
  const auto u2rspos = tc.root.add_root(*u2pos + *rspos);
  const auto u2rsneg = tc.root.add_root(-*u2rspos);
  const auto u2rlpos = tc.root.add_root(*u2pos + *rlpos);
  const auto u2rlneg = tc.root.add_root(-*u2rlpos);
  const auto u3pos = tc.root.add_root(*q3pos * *vpos);
  const auto u3neg = tc.root.add_root(-*u3pos);
  const auto u3rspos = tc.root.add_root(*u3pos + *rspos);
  const auto u3rsneg = tc.root.add_root(-*u3rspos);
  const auto u3rlpos = tc.root.add_root(*u3pos + *rlpos);
  const auto u3rlneg = tc.root.add_root(-*u3rlpos);
  const auto u4pos = tc.root.add_root(*q4pos * *vpos);
  const auto u4neg = tc.root.add_root(-*u4pos);
  const auto u4rspos = tc.root.add_root(*u4pos + *rspos);
  const auto u4rsneg = tc.root.add_root(-*u4rspos);
  const auto u4rlpos = tc.root.add_root(*u4pos + *rlpos);
  const auto u4rlneg = tc.root.add_root(-*u4rlpos);
  const auto u5pos = tc.root.add_root(*q5pos * *vpos);
  const auto u5neg = tc.root.add_root(-*u5pos);
  const auto u5rspos = tc.root.add_root(*u5pos + *rspos);
  const auto u5rsneg = tc.root.add_root(-*u5rspos);
  const auto u5rlpos = tc.root.add_root(*u5pos + *rlpos);
  const auto u5rlneg = tc.root.add_root(-*u5rlpos);

  auto [q, r] = rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(BigintTestAccessor::size(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  // m = 0
  EXPECT_EQ(
      BigintTestAccessor::size(*u0rlpos) - BigintTestAccessor::size(*vpos), 0);
  EXPECT_EQ(BigintTestAccessor::size(*u0pos) - BigintTestAccessor::size(*vpos),
            0);
  std::tie(q, r) = u0pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u0pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u0neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u0neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u0rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u0rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u0rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u0rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u0rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u0rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u0rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u0rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q0pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  // m = 1, 1-word quotient (case 1)
  EXPECT_EQ(BigintTestAccessor::size(*u1pos) - BigintTestAccessor::size(*vpos),
            1);
  EXPECT_EQ(
      BigintTestAccessor::size(*u1rlpos) - BigintTestAccessor::size(*vpos), 1);
  std::tie(q, r) = u1pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u1pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u1neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u1neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u1rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u1rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u1rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u1rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u1rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u1rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u1rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u1rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q1pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  // m = 1, 1-word quotient (case 2)
  EXPECT_EQ(BigintTestAccessor::size(*u2pos) - BigintTestAccessor::size(*vpos),
            1);
  EXPECT_EQ(
      BigintTestAccessor::size(*u2rlpos) - BigintTestAccessor::size(*vpos), 1);
  std::tie(q, r) = u2pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u2pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u2neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u2neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u2rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u2rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u2rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u2rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u2rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u2rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u2rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2neg);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u2rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q2pos);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *rlneg);

  // m = 1, 2-word quotient
  EXPECT_EQ(BigintTestAccessor::size(*u3pos) - BigintTestAccessor::size(*vpos),
            1);
  EXPECT_EQ(
      BigintTestAccessor::size(*u3rlpos) - BigintTestAccessor::size(*vpos), 1);
  std::tie(q, r) = u3pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u3pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u3neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u3neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u3rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u3rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u3rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u3rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u3rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u3rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u3rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3neg);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u3rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q3pos);
  EXPECT_EQ(*r, *rlneg);

  // m > 1, m-word quotient
  EXPECT_GT(BigintTestAccessor::size(*u4pos) - BigintTestAccessor::size(*vpos),
            1);
  EXPECT_EQ(BigintTestAccessor::size(*u4pos) - BigintTestAccessor::size(*vpos),
            BigintTestAccessor::size(*q4pos));
  EXPECT_EQ(
      BigintTestAccessor::size(*u4rlpos) - BigintTestAccessor::size(*vpos),
      BigintTestAccessor::size(*q4pos));
  std::tie(q, r) = u4pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u4pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u4neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u4neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u4rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u4rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u4rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u4rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u4rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u4rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u4rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4neg);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u4rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q4pos);
  EXPECT_EQ(*r, *rlneg);

  // m > 1, m+1-word quotient
  EXPECT_GT(BigintTestAccessor::size(*u5pos) - BigintTestAccessor::size(*vpos),
            2);
  EXPECT_EQ(BigintTestAccessor::size(*u5pos) - BigintTestAccessor::size(*vpos),
            BigintTestAccessor::size(*q5pos) - 1);
  EXPECT_EQ(
      BigintTestAccessor::size(*u5rlpos) - BigintTestAccessor::size(*vpos),
      BigintTestAccessor::size(*q5pos) - 1);
  std::tie(q, r) = u5pos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u5pos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u5neg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u5neg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *zero);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
  EXPECT_EQ(BigintTestAccessor::size(*r), 0);

  std::tie(q, r) = u5rspos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u5rspos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *rspos);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u5rsneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u5rsneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *rsneg);
  EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

  std::tie(q, r) = u5rlpos->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u5rlpos->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *rlpos);

  std::tie(q, r) = u5rlneg->divmod(*vpos);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5neg);
  EXPECT_EQ(*r, *rlneg);

  std::tie(q, r) = u5rlneg->divmod(*vneg);
  tc.root.add_root(q);
  tc.root.add_root(r);
  EXPECT_EQ(*q, *q5pos);
  EXPECT_EQ(*r, *rlneg);
}

// test case: divisor and dividend both at least two words, divisor
// large enough that no shifting is necessary (i.e. highest word is at
// least 2^63)
TEST(BigintTest, LongDivision_Shift) {
  TestContext tc;
  const auto vbase = tc.root.add_root(
      make_managed<bigint>(0xd00db3c001a5a5a5ull, 0xc4f300fff4c4deffull, true));
  const auto zero = tc.root.add_root(make_managed<bigint>());
  const auto rspos = tc.root.add_root(make_managed<bigint>(4500000000ll));
  const auto rsneg = tc.root.add_root(-*rspos);
  const auto rlpos = tc.root.add_root(make_managed<bigint>(1, 1047, true));
  const auto rlneg = tc.root.add_root(-*rlpos);
  const auto q0pos = tc.root.add_root(make_managed<bigint>(1));
  const auto q0neg = tc.root.add_root(-*q0pos);
  const auto q1pos = tc.root.add_root(make_managed<bigint>(92576));
  const auto q1neg = tc.root.add_root(-*q1pos);
  const auto q2pos =
      tc.root.add_root(make_managed<bigint>(0xffffffffffffffffull, true));
  const auto q2neg = tc.root.add_root(-*q2pos);
  const auto q3pos = tc.root.add_root(make_managed<bigint>(1, 888888, true));
  const auto q3neg = tc.root.add_root(-*q3pos);
  auto q4pos = tc.root.add_root(*q0pos << 192);
  q4pos = tc.root.replace_root(q4pos, *q4pos - 1);
  const auto q4neg = tc.root.add_root(-*q4pos);
  const auto q5pos = tc.root.add_root(*q3pos << 128);
  const auto q5neg = tc.root.add_root(-*q5pos);

  for (int i = 1; i < 64; ++i) {
    const auto vpos = tc.root.add_root(*vbase >> i);
    const auto vneg = tc.root.add_root(-*vpos);
    const auto u0pos = tc.root.add_root(*q0pos * *vpos);
    const auto u0neg = tc.root.add_root(-*u0pos);
    const auto u0rspos = tc.root.add_root(*u0pos + *rspos);
    const auto u0rsneg = tc.root.add_root(-*u0rspos);
    const auto u0rlpos = tc.root.add_root(*u0pos + *rlpos);
    const auto u0rlneg = tc.root.add_root(-*u0rlpos);
    const auto u1pos = tc.root.add_root(*q1pos * *vpos);
    const auto u1neg = tc.root.add_root(-*u1pos);
    const auto u1rspos = tc.root.add_root(*u1pos + *rspos);
    const auto u1rsneg = tc.root.add_root(-*u1rspos);
    const auto u1rlpos = tc.root.add_root(*u1pos + *rlpos);
    const auto u1rlneg = tc.root.add_root(-*u1rlpos);
    const auto u2pos = tc.root.add_root(*q2pos * *vpos);
    const auto u2neg = tc.root.add_root(-*u2pos);
    const auto u2rspos = tc.root.add_root(*u2pos + *rspos);
    const auto u2rsneg = tc.root.add_root(-*u2rspos);
    const auto u2rlpos = tc.root.add_root(*u2pos + *rlpos);
    const auto u2rlneg = tc.root.add_root(-*u2rlpos);
    const auto u3pos = tc.root.add_root(*q3pos * *vpos);
    const auto u3neg = tc.root.add_root(-*u3pos);
    const auto u3rspos = tc.root.add_root(*u3pos + *rspos);
    const auto u3rsneg = tc.root.add_root(-*u3rspos);
    const auto u3rlpos = tc.root.add_root(*u3pos + *rlpos);
    const auto u3rlneg = tc.root.add_root(-*u3rlpos);
    const auto u4pos = tc.root.add_root(*q4pos * *vpos);
    const auto u4neg = tc.root.add_root(-*u4pos);
    const auto u4rspos = tc.root.add_root(*u4pos + *rspos);
    const auto u4rsneg = tc.root.add_root(-*u4rspos);
    const auto u4rlpos = tc.root.add_root(*u4pos + *rlpos);
    const auto u4rlneg = tc.root.add_root(-*u4rlpos);
    const auto u5pos = tc.root.add_root(*q5pos * *vpos);
    const auto u5neg = tc.root.add_root(-*u5pos);
    const auto u5rspos = tc.root.add_root(*u5pos + *rspos);
    const auto u5rsneg = tc.root.add_root(-*u5rspos);
    const auto u5rlpos = tc.root.add_root(*u5pos + *rlpos);
    const auto u5rlneg = tc.root.add_root(-*u5rlpos);

    auto [q, r] = rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(BigintTestAccessor::size(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    // m = 0
    EXPECT_EQ(
        BigintTestAccessor::size(*u0rlpos) - BigintTestAccessor::size(*vpos),
        0);
    EXPECT_EQ(
        BigintTestAccessor::size(*u0pos) - BigintTestAccessor::size(*vpos), 0);
    std::tie(q, r) = u0pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u0pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u0neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u0neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u0rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u0rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u0rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u0rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u0rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u0rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u0rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u0rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q0pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    // m = 0 (case 2) or m = 1, 1-word quotient (case 1)
    std::tie(q, r) = u1pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u1pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u1neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u1neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u1rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u1rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u1rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u1rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u1rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u1rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u1rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u1rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q1pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    // m = 1, 1-word quotient (case 2)
    EXPECT_EQ(
        BigintTestAccessor::size(*u2pos) - BigintTestAccessor::size(*vpos), 1);
    EXPECT_EQ(
        BigintTestAccessor::size(*u2rlpos) - BigintTestAccessor::size(*vpos),
        1);
    std::tie(q, r) = u2pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u2pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u2neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u2neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u2rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u2rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u2rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u2rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u2rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u2rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u2rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2neg);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u2rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q2pos);
    EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
    EXPECT_EQ(*r, *rlneg);

    // m = 1, 2-word quotient
    EXPECT_EQ(
        BigintTestAccessor::size(*u3pos) - BigintTestAccessor::size(*vpos), 1);
    EXPECT_EQ(
        BigintTestAccessor::size(*u3rlpos) - BigintTestAccessor::size(*vpos),
        1);
    std::tie(q, r) = u3pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u3pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u3neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u3neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u3rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u3rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u3rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u3rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u3rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u3rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u3rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3neg);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u3rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q3pos);
    EXPECT_EQ(*r, *rlneg);

    // m > 1, m-word quotient
    EXPECT_GT(
        BigintTestAccessor::size(*u4pos) - BigintTestAccessor::size(*vpos), 1);
    EXPECT_EQ(
        BigintTestAccessor::size(*u4pos) - BigintTestAccessor::size(*vpos),
        BigintTestAccessor::size(*q4pos));
    EXPECT_EQ(
        BigintTestAccessor::size(*u4rlpos) - BigintTestAccessor::size(*vpos),
        BigintTestAccessor::size(*q4pos));
    std::tie(q, r) = u4pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u4pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u4neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u4neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u4rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u4rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u4rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u4rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u4rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u4rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u4rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4neg);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u4rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q4pos);
    EXPECT_EQ(*r, *rlneg);

    // m > 1, m+1-word quotient
    EXPECT_GT(
        BigintTestAccessor::size(*u5pos) - BigintTestAccessor::size(*vpos), 2);
    EXPECT_EQ(
        BigintTestAccessor::size(*u5pos) - BigintTestAccessor::size(*vpos),
        BigintTestAccessor::size(*q5pos) - 1);
    EXPECT_EQ(
        BigintTestAccessor::size(*u5rlpos) - BigintTestAccessor::size(*vpos),
        BigintTestAccessor::size(*q5pos) - 1);
    std::tie(q, r) = u5pos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u5pos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u5neg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u5neg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *zero);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);
    EXPECT_EQ(BigintTestAccessor::size(*r), 0);

    std::tie(q, r) = u5rspos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u5rspos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *rspos);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u5rsneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u5rsneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *rsneg);
    EXPECT_EQ(BigintTestAccessor::capacity(*r), 0);

    std::tie(q, r) = u5rlpos->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u5rlpos->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *rlpos);

    std::tie(q, r) = u5rlneg->divmod(*vpos);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5neg);
    EXPECT_EQ(*r, *rlneg);

    std::tie(q, r) = u5rlneg->divmod(*vneg);
    tc.root.add_root(q);
    tc.root.add_root(r);
    EXPECT_EQ(*q, *q5pos);
    EXPECT_EQ(*r, *rlneg);
  }
}

// test case: Triggers the D6 condition when the divisor requires no
// shift; that is, when qhat is an overestimate of a word of the
// quotient and the most significant word of the divisor is between
// 2^63 and 2^64.
TEST(BigintTest, Division_D6_NoShift) {
  TestContext tc;
  managed_ptr<bigint> v;

  // m == 0 can't trigger because the divisor would have to be greater
  // than the dividend, which triggers a different condition.
  //
  // m == 1, len(q) == 2 can't trigger because the dividend maxes out
  // at 2^(64 * (m + n)) - 1 and the divisor is at least 2^(64*(n-1)),
  // so the quotient is less than 2^(64*m). For the same reason, m ==
  // 2, len(q) == 3 can't trigger.

  // m == 1, len(q) == 1
  managed_ptr<bigint> u11;
  managed_ptr<bigint> q11;
  managed_ptr<bigint> r11;
  // m == 2, len(q) == 2
  managed_ptr<bigint> u22;
  managed_ptr<bigint> q22;
  managed_ptr<bigint> r22;
  {
    auto hold = ctx().mgr->acquire_hold();
    v = *(bigint(1) << 191) + *(bigint(1, 0, true) - 1);
    EXPECT_EQ(BigintTestAccessor::size(*v), 3);
    tc.root.add_root(v);

    u11 = bigint(1) << 253;
    EXPECT_EQ(BigintTestAccessor::size(*u11), 4);
    q11 = make_managed<bigint>(0x3FFFFFFFFFFFFFFFull, true);
    r11 = *(bigint(0x7FFFFFFFFFFFFFFFull, true) << 128) +
          bigint(0xC000000000000001ull, 0x3FFFFFFFFFFFFFFFull, true);
    EXPECT_EQ(*u11, *(*(*q11 * *v) + *r11));
    tc.root.add_root(u11);
    tc.root.add_root(q11);
    tc.root.add_root(r11);

    u22 = *u11 << 64;
    q22 = make_managed<bigint>(0x3FFFFFFFFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull,
                               true);
    r22 = *(bigint(1ull << 62, true) << 128) +
          bigint(1ull << 62, 0xFFFFFFFFFFFFFFFFull, true);
    EXPECT_EQ(*u22, *(*(*q22 * *v) + *r22));
    tc.root.add_root(u22);
    tc.root.add_root(q22);
    tc.root.add_root(r22);
  }

  auto [q, r] = u11->divmod(*v);
  EXPECT_EQ(*q, *q11) << "u: " << u11 << ", v: " << v;
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *r11) << "u: " << u11 << ", v: " << v;

  std::tie(q, r) = u22->divmod(*v);
  EXPECT_EQ(*q, *q22) << "u: " << u22 << ", v: " << v;
  EXPECT_EQ(*r, *r22) << "u: " << u22 << ", v: " << v;
}

// test case: Triggers the D6 condition when the divisor requires a
// shift; that is, when qhat is an overestimate of a word of the
// quotient and the most significant word of the divisor is less than
// 2^63.
TEST(BigintTest, Division_D6_Shift) {
  TestContext tc;
  managed_ptr<bigint> v;
  // m == 0
  managed_ptr<bigint> u0;
  managed_ptr<bigint> q0;
  managed_ptr<bigint> r0;
  // m == 1, len(q) == 1
  managed_ptr<bigint> u11;
  managed_ptr<bigint> q11;
  managed_ptr<bigint> r11;
  // m == 1, len(q) == 2
  managed_ptr<bigint> u12;
  managed_ptr<bigint> q12;
  managed_ptr<bigint> r12;
  // m == 2, len(q) == 2
  managed_ptr<bigint> u22;
  managed_ptr<bigint> q22;
  managed_ptr<bigint> r22;
  // m == 2, len(q) == 3
  managed_ptr<bigint> u23;
  managed_ptr<bigint> q23;
  managed_ptr<bigint> r23;
  {
    auto hold = ctx().mgr->acquire_hold();
    v = *(bigint(1) << 183) + 0xFFFFFFFFFFFFFFll;
    EXPECT_EQ(BigintTestAccessor::size(*v), 3);
    tc.root.add_root(v);

    u0 = bigint(1) << 189;
    EXPECT_EQ(BigintTestAccessor::size(*u0), 3);
    q0 = make_managed<bigint>(0x3Fll);
    r0 = *(bigint(0x7FFFFFFFFFFFFFll) << 128) +
         bigint(0xFFFFFFFFFFFFFFFFull, 0xC10000000000003Full, true);
    EXPECT_EQ(*u0, *(*(*q0 * *v) + *r0));
    tc.root.add_root(u0);
    tc.root.add_root(q0);
    tc.root.add_root(r0);

    u11 = bigint(1) << 221;
    EXPECT_EQ(BigintTestAccessor::size(*u11), 4);
    q11 = make_managed<bigint>(0x3FFFFFFFFFull, true);
    r11 = *(bigint(0x7FFFFFFFFFFFFFll) << 128) +
          bigint(0xFFFFFFFFC0000000ull, 0x0100003FFFFFFFFFull, true);
    EXPECT_EQ(*u11, *(*(*q11 * *v) + *r11));
    tc.root.add_root(u11);
    tc.root.add_root(q11);
    tc.root.add_root(r11);

    u12 = bigint(1) << 253;
    EXPECT_EQ(BigintTestAccessor::size(*u12), 4);
    q12 = make_managed<bigint>(0x3Full, 0xFFFFFFFFFFFFFFFFull, true);
    r12 = *(bigint(0x7FFFFFFFFFFFFFll) << 128) +
          bigint(0xC000000000000040ull, 0xFFFFFFFFFFFFFFull, true);
    EXPECT_EQ(*u12, *(*(*q12 * *v) + *r12));
    tc.root.add_root(u12);
    tc.root.add_root(q12);
    tc.root.add_root(r12);

    u22 = *u11 << 64;
    EXPECT_EQ(BigintTestAccessor::size(*u22), 5);
    q22 = make_managed<bigint>(0x3FFFFFFFFFull, 0xFFFFFFFFFFFFFFFFull, true);
    r22 = *(bigint(0x7FFFFFC0000000ll) << 128) +
          bigint(0x4000000000ull, 0xFFFFFFFFFFFFFFull, true);
    EXPECT_EQ(*u22, *(*(*q22 * *v) + *r22));
    tc.root.add_root(u22);
    tc.root.add_root(q22);
    tc.root.add_root(r22);

    u23 = bigint(15) << 316;
    EXPECT_EQ(BigintTestAccessor::size(*u23), 5);
    q23 = *(bigint(0x1DFll) << 128) +
          bigint(0xFFFFFFFFFFFFFFFFull, 0xFFFFFFFFFFFFFC40ull, true);
    r23 = *(bigint(0x1E0) << 128) + bigint(3ull, 0xBFFFFFFFFFFFFC40ull, true);
    EXPECT_EQ(*u23, *(*(*q23 * *v) + *r23));
    tc.root.add_root(u23);
    tc.root.add_root(q23);
    tc.root.add_root(r23);
  }

  auto [q, r] = u0->divmod(*v);
  EXPECT_EQ(*q, *q0) << "u: " << u0 << ", v: " << v;
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *r0) << "u: " << u0 << ", v: " << v;

  std::tie(q, r) = u11->divmod(*v);
  EXPECT_EQ(*q, *q11) << "u: " << u11 << ", v: " << v;
  EXPECT_EQ(BigintTestAccessor::size(*q), 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*q), 0);
  EXPECT_EQ(*r, *r11) << "u: " << u11 << ", v: " << v;

  std::tie(q, r) = u12->divmod(*v);
  EXPECT_EQ(*q, *q12) << "u: " << u12 << ", v: " << v;
  EXPECT_EQ(*r, *r12) << "u: " << u12 << ", v: " << v;

  std::tie(q, r) = u22->divmod(*v);
  EXPECT_EQ(*q, *q22) << "u: " << u22 << ", v: " << v;
  EXPECT_EQ(*r, *r22) << "u: " << u22 << ", v: " << v;

  std::tie(q, r) = u23->divmod(*v);
  EXPECT_EQ(*q, *q23) << "u: " << u23 << ", v: " << v;
  EXPECT_EQ(*r, *r23) << "u: " << u23 << ", v: " << v;
}

TEST(BigintTest, ParseBigintBinary) {
  TestContext tc;
  auto b = tc.root.add_root(parse_bigint_binary(u8"0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::size(*b), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary(u8"-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::size(*b), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary(u8"1"));
  EXPECT_EQ(*b, 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary(u8"-1"));
  EXPECT_EQ(*b, -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary(u8"00001"));
  EXPECT_EQ(*b, 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary(u8"-00001"));
  EXPECT_EQ(*b, -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b, parse_bigint_binary(u8"11111110110111001011101010011000011101100101010"
                             u8"00011001000010000"));
  EXPECT_EQ(b->to_string(), "FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b, parse_bigint_binary(u8"-1111111011011100101110101001100001110110010101"
                             u8"000011001000010000"));
  EXPECT_EQ(b->to_string(), "-FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(u8"0000001111111011011100101110101001100001110110010"
                          "101000011001000010000"));
  EXPECT_EQ(b->to_string(), "FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(u8"-000000111111101101110010111010100110000111011001"
                          "0101000011001000010000"));
  EXPECT_EQ(b->to_string(), "-FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b, parse_bigint_binary(u8"11111111011011100101110101001100001110110010101"
                             u8"000011001000010000"));
  EXPECT_EQ(b->to_string(), "1FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(u8"-111111110110111001011101010011000011101100101010"
                          "00011001000010000"));
  EXPECT_EQ(b->to_string(), "-1FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  EXPECT_THROW(b = parse_bigint_binary(u8""), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary(u8"-"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary(u8"--0"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary(u8"0-0"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary(u8"121"), std::invalid_argument);
}

TEST(BigintTest, ParseBigintOctal) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_octal(u8"0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal(u8"0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal(u8"-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal(u8"-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::oct;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_octal(to_u8string(os.str())));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_octal(to_u8string(os.str())));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_octal(u8"1777777777777777777777"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b,
                           parse_bigint_octal(u8"0001777777777777777777777"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal(u8"-1777777777777777777777"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b,
                           parse_bigint_octal(u8"-0001777777777777777777777"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal(u8"2000000000000000000000"));
  EXPECT_EQ(b->to_string(), "10000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_octal(u8"3777777777777777777777777777777777777777777"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_octal(u8"4000000000000000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b, parse_bigint_octal(u8"777777777777777777777777777777777777777777777777"
                            u8"7777777777777777"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b, parse_bigint_octal(u8"100000000000000000000000000000000000000000000000"
                            u8"00000000000000000"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 4);
}

TEST(BigintTest, ParseBigintHex) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_hex(u8"0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::hex << std::nouppercase;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_hex(to_u8string(os.str())));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_hex(to_u8string(os.str())));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  os << std::hex << std::uppercase;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_hex(to_u8string(os.str())));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_hex(to_u8string(os.str())));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_hex(u8"FFFFFFFFFFFFFFFF"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"000ffffffffffffffff"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"-FFFFFFFFFFFFFFFF"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"-000ffffffffffffffff"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex(u8"10000000000000000"));
  EXPECT_EQ(b->to_string(), "10000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_hex(u8"FFFFFFFFFFFFFFFFffffffffffffffff"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_hex(u8"100000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b,
      parse_bigint_hex(u8"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b,
      parse_bigint_hex(u8"1000000000000000000000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 4);
}

TEST(BigintTest, ParseBigintDecimal) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_decimal(u8"0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::dec;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_decimal(to_u8string(os.str())));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_decimal(to_u8string(os.str())));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"18446744073709551615"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b,
                           parse_bigint_decimal(u8"00018446744073709551615"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"-18446744073709551615"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b,
                           parse_bigint_decimal(u8"-00018446744073709551615"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal(u8"18446744073709551616"));
  EXPECT_EQ(b->to_string(), "10000000000000000");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(u8"340282366920938463463374607431768211455"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(u8"340282366920938463463374607431768211456"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(
             u8"6277101735386680763835789423207666416102355444464034512895"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(
             u8"6277101735386680763835789423207666416102355444464034512896"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");

  std::u8string large_number_decimal =
      u8"5236350777678770092811398442789248657037165192974544359320302129945496"
      u8"0016882447215175852246806672321132045650431867557472428031634259067054"
      u8"1758818271826016783781688871439202710354161967598080183593606827466955"
      u8"8106791266800199284959450712200799606171888563546107313259678846346109"
      u8"0681904285084596180105749376934718810089969737958292959026512217168455"
      u8"9455117622431130703671011120556444566563008771382102770835651640158132"
      u8"6161084044530756292655034645611629556651882108047701371547009112144150"
      u8"0756019667102698522498455574548935471143779791490994527822496587985822"
      u8"0937013194890236760135622347873549858434401378507951803564469909785448"
      u8"2609037076858223870681211156240592598060468054021254233861865527153728"
      u8"6793873768443967663777409777056073842030970330877241682925813588444703"
      u8"6931556363933289689710331801421577865587481931198494571916955054088572"
      u8"2841994500700899790469450474128747906429957146181352442895065241469729"
      u8"6832889041986984362967652128627279826999721074538018331871257158104875"
      u8"1410278753814099561434250897497761752958609852825782037029620323985136"
      u8"2938862753717335806606423377622404081376844850959847577429559487786076"
      u8"0111687712369392240806444679105239118354624832825744780415995614573813"
      u8"2685492011739046180602991191855277601942854668240110281607125202404395"
      u8"8600561672399950618236070139535919279212292360450730748154151725554214"
      u8"6267248831357153767999867067266100473388774869211794736457118817413015"
      u8"5454935532306738731482994216395224300451502056673161764183683138692802"
      u8"7068862126247465842140503860730308283195400625127471312840180202687403"
      u8"3385075809911458985536005118666854559342532958364856822541503878876697"
      u8"4636103759586150119863993961668391203765779237638245624614756285199847"
      u8"4689226816821891421701996745207940264433658778833691428967944701192519"
      u8"7650898854477952097966000937513111375939890844655280117281034495394870"
      u8"5758899405742689923980169328441024958881919509595467593889264231036562"
      u8"6134775025241141542012534287403713827829782248496993269990065500819667"
      u8"0545254996920148017071874278801991770928815192173944641456703168740094"
      u8"2217843093914757879540513773233201557877513245849034421363340077192365"
      u8"5573159012003395167556400205504589251357144303835091401429193883255821"
      u8"0854219952664653264945628563046911266775227470721522674457611308082326"
      u8"8955528680050942596328539398148616305229868150406697162719879370498304"
      u8"5552949762256013302264381029553567445923446164907146699354529387834651"
      u8"7807267781440403797916144841890101719210813589116162787197772846412328"
      u8"1519522611542685306447781978291149447080039534829231332492190150740967"
      u8"5122437097951627380406764234096693728664061328857616914655427490493530"
      u8"2997771558933446349417852723141156292369984285517617512196470512639015"
      u8"9624955712791856119378981260012252979071724997201012163472329761536090"
      u8"1543117374649006146337318387416544365281999423604973018483093198843648"
      u8"2167955548726507741202071436196070188520359017499144869798103269935932"
      u8"5794128693568734443983929961356364512033130523098451632247252254159053"
      u8"6283669325174985679598069511507433871189199214180474436517216301706514"
      u8"3561516536452205703116427180397188480403754276236801674948352639820328"
      u8"3133641247494923419452833262547514614518095956889047008655339651373745"
      u8"4113746422944368362903267739901284375058193585982435768864474791400841"
      u8"4037438979349930087716106846662762350042853590574200096865870411795232"
      u8"0101448594759057026479374056725532309440160576616256233350414978512145"
      u8"2490344686666507627825707498555557103229619670962018393059890766965995"
      u8"8876434848845669307489436816919622120002646874119087622020232952682482"
      u8"0092326469929241216049109325229430945338487867869477503199357032932405"
      u8"4970206385752534131557933621873285244731334659526189338010903487371069"
      u8"4451564652377995210416404185100813473744418051314210539677287049740349"
      u8"1922714104667743080135562863088343232259419603853823797972896160568296"
      u8"0514120690029620269119527133942793128358598027205724695300762847631708"
      u8"4930034065425411413997603591515482964842668040581302562253003712186819"
      u8"9535859820419063310478456994764774616618446687139397104085445971764930"
      u8"5635369652393147549734872241547233906664995096570634944881407229045644"
      u8"7789073673370744962482763447857536016866295653607196887692483188929206"
      u8"0473134364681366105897747785082957839362671509777268248952079682495270"
      u8"1492743291687191789138293599989501405647401182046832121933772567685651"
      u8"0305621913296504990172070311271723552633345238315181683203320099762062"
      u8"4043471132301758871540045675891109211335223254062345892356433879123939"
      u8"0535321782069093467463484933208540898388991922678505930160365710319081"
      u8"4876178890959023089808523642284203274709742337615511929506177876095344"
      u8"2313668650156253983202076406016621044241536986884668746684697189873811"
      u8"8937202105357357633037576921547833171401067350904719718941266868741397"
      u8"6631031647635824449915833914057567300761121213923692135741355586003305"
      u8"2383539591040499571710881788858563612841983437871345109331058900698076"
      u8"6921714292360136531116592685825874119176783840776058647254163652707943"
      u8"8223190990456193581010614376708672899289495497261577923161194855124891"
      u8"3294441006402311387319399859555206889176340224450925120197411187439533"
      u8"7608969519186402672169943482774540294679043434909583269307792701136901"
      u8"6067117922307383603825370087494804470126979834011073310172720978002132"
      u8"7866018221042395495298514315063213687849232786170642546762292827804522"
      u8"1335328926203357806992686759021145585997208517192276475307033837187436"
      u8"3424958975470929390816145231247415545390413249948012316792236889068898"
      u8"2026394430949871228681980507071118460064465200759503828802206521125594"
      u8"2432890075082332555050711523440210877628764347871858059039776640069033"
      u8"7317470091719147882709820880287925395506257986888585253499190130297182"
      u8"0189466118343252690999106428237866728114463372655184468962540829174280"
      u8"0418670117510738933874052933134049961570033660693279148014295720275179"
      u8"3396857356224412990276944194011708850173206785933527534703035633230611"
      u8"3354285923733091423904028501839896432773677853407708930400182070188771"
      u8"6014834641824350649409537065900786903466875773917004085954243279982599"
      u8"7350893154694900516077231062408202969089272302943915159621956055885547"
      u8"4879268802502646844397041769252905013450412702053030838712761261006020"
      u8"0475953190841361780280170915278194864238645088744075725299993746406116"
      u8"5658185566275509557692233571660779204836862268807516582756035561721343"
      u8"3738597044497478126699907664861251501361157287334164680845488814245093"
      u8"1658688054901070427287982539888798893759788875626043576375061314024966"
      u8"5723646475759015018753601795585271626531035543620936647286479794895236"
      u8"3874284603567039301466284047688938563237290326026763793907858111612419"
      u8"0718006048584786099789186339731467553163308601867932917531008268187626"
      u8"5957725215440683418028207595460663477592291104736709510960167913955022"
      u8"2167746950580238705332018709034201488839871060036690347934664352889832"
      u8"5158750608231316652410404889678249344151041204393719542931725186740584"
      u8"7032910844562305564614147687479720721664034191114185525427300432066471"
      u8"1920125028070769842909378361850300681805613479676837906853124874511673"
      u8"1434646432818888685866608334753615597207438562951934275577151219163844"
      u8"1482823994435490867900198038949464599878068711725929533744723835601405"
      u8"0692763969757590203448618244306704715314914721758411045757555742179324"
      u8"9668107488326248272332303721017609883653961409797452818262479597640084"
      u8"7432429837612581188024293086453861798497366668421094906457324745507943"
      u8"8022544435950806138763790937270549910824227565442902410143736481190552"
      u8"3354473948581664708547263561402961536959154429372978712790461809177911"
      u8"7531528656884983336648895930443593476857949380553079207003625523872380"
      u8"3205954579748401081885210434974449326568025905479828449047447522292956"
      u8"6155163745770852813663940237148947900864167623554121036775270003257427"
      u8"7450162728248654241060184100474715220133405347365389992171451861591397"
      u8"0081016876581121268351829960649046406726179633186297819293370300447482"
      u8"3210055345255772651214764482204866280674181218448407026820991701191786"
      u8"9080519336934529804447436037689451313310185256027936190394819824204124"
      u8"4896845354740815482923032443731820863491374477294787322108114668629930"
      u8"8795324697208438239314033027772422868089360329899847194674521399429935"
      u8"8064746754602974077189447780363825379245478132056975539814418764126927"
      u8"3679055927587779398505726852929495006108859734754447369360601273463158"
      u8"9686718484183839563836857099998208760533306032295492097417945415701767"
      u8"3474161468611341252777436122524303324127006117132111926765606661929677"
      u8"4700868258453605340329243248959819906840900766431232966756188148193598"
      u8"4268438796653923506177215647575422206962958005664543560322468874828658"
      u8"9371887492808808945367216138500220307401771348736010117475303188688762"
      u8"9943786498389357863574473488839879464091086997281069443976935927422632"
      u8"7796706494102377909078240929871098064369349845613287565651739776536159"
      u8"3743960722576532308091622112869448093418712183960862488663367815280773"
      u8"8377004411356109688100871552342435565880871865196209090032165039330770"
      u8"0554376963937046941114038651943140594474002676168767751787607418807896"
      u8"9041168053858423361473653350098592516059277115618367236567805837212666"
      u8"3083438089234451212816867051423542313607343715053247402550418851723629"
      u8"9547758874858433992221160970121232907446307249239468946139558357536187"
      u8"0941899529610422696990588252993113134288822026999295046950235147950697"
      u8"4690642573728248442889216284836343369193916091206539495604769407461730"
      u8"1160570192966877504846369581977139204175930554401816645012110338670316"
      u8"4240977170101755804759718349196637232951295669988802323348732283840823"
      u8"1127129204605955884820947537751082705458134870651261004982290092455407"
      u8"9807984893931939384700754194888565225251764109724282819006816898533221"
      u8"7291694028859210165323769740551248127883280972291869800392025732368004"
      u8"9823830006924240952088540212709541391379122501479934349284746280274914"
      u8"3130001759948413237293111718861322790130457796047997903392975446741082"
      u8"8895721334107673695813777790906465132490192736035730499374078367076563"
      u8"0935625339744141565510580445423624440052909724252738395035165678427247"
      u8"7619192323249825399485230014871834725571204359884891667800708423069070"
      u8"2920870150558204201523913649237509831774711631590890111981793249827596"
      u8"5587510524982528450758425311484997384074462717221442644571174548663697"
      u8"4654699238884047737477752091448898843991602088685214528942742924383165"
      u8"2372900483386424307160340644748922398842767433394418944970403766330240"
      u8"9929626558489525273051868429183755170407813611167671756317290527381010"
      u8"5765962297036208180740553478327708824502542762857468773450740138500189"
      u8"9884538717770594299568182204044038956294920672450062313618440041173163"
      u8"5446438668836394980620137631091971052861655556518418739828868120424799"
      u8"4389561906702150288438481002039338117591082864544299263123472948610512"
      u8"2320067160535951978257183751398304785460336402840039936798184149169678"
      u8"3354279390422179650800326438781072978892108808187823741110462276831864"
      u8"1731345317956798588631468899507129836845582975341996186434395196976234"
      u8"1976838243777286188004048895621940035961359214647120573688133375161060"
      u8"5341827028722527302765749589902352702958432338035911514395301647828663"
      u8"8171156236386774983782302164368682223139614136715748508515753852429763"
      u8"2073510089106647136238153116670702762333798225803412250281643925656031"
      u8"9043062983519275732910028553711218011426860637113074763219127013150758"
      u8"4631483766512248522641307357545235759556467808900835350353560121176601"
      u8"3370362646634233755275291276630275117979437589835933777630177574457873"
      u8"9788289759425100367877492020326250839486672421885651981037238271042248"
      u8"3099564743484146541767011604790191055588034107850757070354088521994816"
      u8"9607714321544712353631222673618716111446072220300379312161336997102158"
      u8"0825417976764954019747076972102324530492928376155806685143707478451552"
      u8"2496975149679328785645866738085858863130423919299988880888289664565317"
      u8"1757114452390446065677671424384328413079328329848440360498284468494097"
      u8"7679415249698874693587038419827984751189400707278575962058786012485017"
      u8"0082855628928642816961373322110396962697614640242829118070439200293015"
      u8"5682871509866619896252845577841269238108359229179196588655846326733890"
      u8"9112814695143684917858330766202750998341807779068669811037925165424848"
      u8"7407774560444695931511692454868196204552204055146765979884814528193210"
      u8"3928289932366145163704196250570118807135734480326547916965199061377615"
      u8"4457450796946447549038705069082124751299401768293874032808712809003803"
      u8"9272776887420678462833937675503336524614425168096641875549489204116536"
      u8"1557500380479539537057962230305656392291299554899295451686961448032528"
      u8"5604824927808420641067732286840695842737214945855137738901097834271303"
      u8"5751662910555580789321062415908481483692265228222268164872887949415968"
      u8"5021536401737558493311417966444823708218956028585785112466516384249057"
      u8"5962890992649493596111044524794619702826846698341148990352962554424639"
      u8"5079540068575712784535917029530685738624774228206761897018555325160608"
      u8"7705571199907878767750171795191766982106819621003052055369888454152634"
      u8"9624255364725950030408347945700238430427705235656058475853718727280170"
      u8"1282315288114300528914994348263409690429016772743104615353842807710683"
      u8"2912664296821924229479118925203212377837368596189650281840699157832317"
      u8"4055114502841651276776700928642591785154433397659623896877232398881070"
      u8"3807573886005502961135515505631238086400939136283601016206706050640817"
      u8"6980141303685224027168247668490630891598568796095817056896244641864068"
      u8"9740975692145708591959636025299359680858582135145614977446655711744357"
      u8"4971597227435210758052521239158338722233691486888924199454603821795492"
      u8"8370659466652269693671269267441926182183830612033735773596519980832787"
      u8"5061205932380906298780997655592739133587646798325613466021707190066096"
      u8"0630917941994787697107905268317044855872782218344295434403699165487321"
      u8"9371726195407391044163369830514232557521758686617157889243033728055457"
      u8"7165532972539336965664369007685252128585942113061583908267380107238236"
      u8"2865282305419057369351810647004009793033489197100221173694348507175368"
      u8"2905148355549179604543505382660759799809273519772187646873670235155608"
      u8"2369506600220034095425796284464173825789591898534741584797442172006348"
      u8"7372007797049290020044915912673392000900080291341707632742366280878357"
      u8"9899227736838671025217508149759368239774108174954530304709395934909481"
      u8"1018109637973379203192872204206601577125692364186524716784658317005969"
      u8"9463841818108249700210697903076216061073045514608990833081919256632535"
      u8"8396665600085739925136532574634859100897601917323734040964701082368951"
      u8"3905339189226598760618030593290755937712360045087567523721163933370260"
      u8"7451185262454662634363748450410642275636177719031568858598025693075993"
      u8"3572483138198581646301976072973624500122939476055406164938003620845278"
      u8"2334688768160593442722262288492087983536347385198067678805534644680861"
      u8"4376257858750916329561354207187940775876529457225528752431229686575680"
      u8"5702624299651639864318964351088626119925521576689330548547844047113292"
      u8"5442287792479471084985082688884969553476379520163483555408703324244274"
      u8"7467448845183476252902401374480525050372453106479432645346848142430875"
      u8"3127970218952904401447322492449773884811482088463495990227573475894332"
      u8"5888760971235816662036062514794744766071677636272682453529964323146728"
      u8"8563867242580737890289871733649015886277632736351889361281546952682802"
      u8"9373922941103481864268199787281239832144531388633528120951771887784205"
      u8"4410844655479788646366819474518773809098034184007701231493423541855329"
      u8"7039565539866419434395998722628853829200510131745651304222000655364274"
      u8"2619381907289167775474821238496930381121032486378010284011646823857217"
      u8"9073611212742945583850498887349721181315426739595786947621271946503905"
      u8"2096277221799341009189725904649334687529978539239606669766314008073914"
      u8"6450895567923678652426121666643106080255051963464030698822062062790624"
      u8"8990035838158068846888225003890367707034834136972187182412838769121793"
      u8"4864932486396079388057450285654675586278423694356227228166108359775009"
      u8"9608361544596310848087404527654441083684748348081943971429779979931634"
      u8"9582806334227562712058948601008719976702539860722003303858929293021447"
      u8"6200087987829973444463678539829002678225204079774947935897351429745693"
      u8"7748333660118421488076158317260731571736890854254666152214798571433349"
      u8"7616404633738491234178081875287745917582052589007900276529150698104248"
      u8"2190560860835077636456564892512003343386313779762415543026680074731843"
      u8"8708501002296376986549188863750841046701786916613151264444827859796413"
      u8"6310967485545418275269549573088233990226156197699516740373461079609779"
      u8"6367650489703238739117802768349050954489452023389632062620332478421038"
      u8"2482023864987901820046147724851983385398212419462132328030705228536454"
      u8"8005665356200614677885428170256078481504379477429346035354493486924864"
      u8"8586286938887580137287087057604360665759700604183991130465925734785810"
      u8"7051899294494954624374594085648900984008501267957857787017385110597508"
      u8"5365088579059754288447705765579975555205848972810648644530968219379409"
      u8"9518238667390349547375952338089940984421646306031771387185607538731779"
      u8"2891874752227519379233086594108661066463608423992749378455766766403423"
      u8"7791061495234324838523893682915007368447217705702037725028493357216858"
      u8"0201410122849669620008629020108914657286319833619925888744611516339570"
      u8"2492227513101273045125373174316172465933337307204998345671656624725571"
      u8"3010569376835565256592068227997472179622907809424759968378620716038210"
      u8"7405139094738886506310391522044248110234538387007158220536445516909353"
      u8"9054610144370957315339291536262461114597079222272752401872564889643103"
      u8"4779019309839365096242820396096751690883296929079562894082038705958585"
      u8"4962474663910805295791326294732077849435131570602349067540743007927872"
      u8"3558274317403333691931311676070383464477693468873981626664831412357981"
      u8"9299381744536620951115542565670902980151873244014670979219831256554143"
      u8"6132047612712142996396341215983934659102362984322617780237042167187487"
      u8"7679882925543146062667511380427595208861101738767103107010514469081848"
      u8"1959336139020483343514049221488300838594936419666222092281587288830971"
      u8"6682455639687280225898708122529863277458385387890190787164635397426329"
      u8"6870685852024996512195038617930359517215222346329943337638972863600857"
      u8"5491116365726653791667172021896587286501982499699856576729214525928588"
      u8"6911211236266647747244448913903983987228097241446438455541851936368990"
      u8"6706606451513886763119702020831315588644587902290287237756446716197013"
      u8"2425011565015491162112095016264333421626763697523278337293148903578264"
      u8"1388370675534401163534589943189759650009711758046217008555673405015123"
      u8"8770705228358405465563155696042356168565954833185820027120911387648538"
      u8"4153495872221135316579712004326684485284265573466874655198651306110483"
      u8"6577300733705439482643827747472153323229098360954448686563982971321834"
      u8"2203828328392828947846330274581405806275996870821819114218271080239548"
      u8"8820438477952171665409098827245106424738811882102310495687239733722986"
      u8"9577605197336035015751336903152936476848541751431900337260478345328589"
      u8"0931114939124572469924196863292297142486937606467155206729210174335778"
      u8"5863086947889179893955647731154076195771805264689208474758399075080150"
      u8"5126378622428365924748631644582659547542712367038536120807718672393872"
      u8"4627603053426045079121518189550589525231213272683157798915821021885616"
      u8"2083649278298259829133168472799129282032693366160010911524633481984272"
      u8"8616434358787530576656860285413537944290277647733919192659686987560224"
      u8"6135973932550743172243783267115474881780096504174953571244333865988315"
      u8"4073575906071506583772687303855177282302715356600816345016968084925644"
      u8"9269174361482165004829278282671582263354028429606178745330588340763399"
      u8"0517439626111210749634244279758952265744795001361338599819331855174632"
      u8"6562842445448813704596485521807521125633948755227510290685879027971049"
      u8"3141287784260922064517604613931730760002172868586283594895294701889777"
      u8"3100417657318099203591816764591046624619940926039728479702315273840310"
      u8"2064983633497129818958278704357667841306229811661068424958619603426052"
      u8"3507239528790983953955241970148828859221868293006621480529631342343724"
      u8"0932735713214048893760387235378671351867308921286234346639202346645225"
      u8"2872634289351158876582625602009064402850226938080938724363009901378826"
      u8"0295162949458460056774472780834705594924947387099111117576733514516547"
      u8"7516359422293602717271208946579985759825911536891058782304366555150282"
      u8"3020782976455360684245929177763355595734031773929661485773199162486501"
      u8"2489356591690648349326433868419153297493015491298606670317462308517658"
      u8"4753173794007335954659067902814902466180226652671147130813333592735784"
      u8"8891416790774757990283923054080403565962000433697481763507652413605132"
      u8"9989979864979334484508695494831335244824639220675735464180781204999287"
      u8"3819860092452098897279803557288706247749597788401206360734903268215869"
      u8"8571220646325018217417275629318559693126740643887032488585064727289009"
      u8"9430338969598128910941411743205768566369137515622362488418830583811142"
      u8"5377606472386259819637078993804858144161613175110995299544192776001740"
      u8"5774642689598095782808384270501981312762322895611082210829133654440971"
      u8"0505050876981882009076705862767943045040587308529008049048450888920344"
      u8"6331915877249948337002125456519183055943773436728998270883003461807372"
      u8"2766448525264552065734720087046910509226232624013526453142354953065124"
      u8"2129260420788566333114252444195668289944624023132991835821870858332683"
      u8"9711128305922350932132213395914572007514567903477510639529530153704499"
      u8"4665268946989373072455329630505296413439645206320903716808877287534840"
      u8"9630837136585542254115530289984949543339537993409630927316322611596689"
      u8"7621944746675434373180912191003964198383527986549249739296138910164354"
      u8"0357546410032480429396288717244084116641963497192579862425568018727463"
      u8"4953707669308817048614504206623790163690147759261516768443335006009532"
      u8"1076337643434460057228819276885306885120454360933790938499608587297174"
      u8"3385143507999566419964489086637440598742445836479384625391920425871286"
      u8"7038178515019218900554237794954943298549787578919257333801471688784350"
      u8"8445766116778043827542354366893472755003848069520973906713768752569949"
      u8"7130907869763075881520223133162016176573144683740506735769275875343266"
      u8"9011486320012186980133078232974963098258447807737538119962604380514961"
      u8"9361753767654086127658025422145241236258063132284002383289995406797573"
      u8"5497582463347382932062856563852555633442734531908431349524779427242111"
      u8"9247372401713142778139702793815316531862214236652913122818790863132426"
      u8"8356430254558088299017969941791263653621580814909972480967551578139829"
      u8"2232469040774952421354258021207696778764978746477015750693356650788919"
      u8"8346389290855518246002912700329173144154981622382298091433993303620443"
      u8"1101604362248904745982261024071226734505163966704404495035705154318888"
      u8"3660264234377761628517811778005318131574292388832774797507964061777423"
      u8"4928026081601257342692259960320737091989236350672668804776175232713277"
      u8"8505611028111876195562927401582728178197032011736339362280564988725983"
      u8"2491412909657301187316990624987717503810312440213547769525511648630090"
      u8"1317597838849821728976595351258418187635340553877441759400969929822173"
      u8"6646372973275702320926335889549567175113445328620278534482774452403518"
      u8"1770383761502578448859733790024128348795888244858019684706012884318863"
      u8"8671267414690798511691077776415283957428333454737427110507258015036767"
      u8"0578457182913742445663627478785196012474992483404469749235409878935490"
      u8"8552810397986251154539403090610346185861941994751919220000984897538542"
      u8"0190806771735803350578905610012053980977441449301973649636554414289625"
      u8"9725802740796196361215194864297501979462223514726359568117474759593486"
      u8"2776011887488724820508299135464699161719782830872577622032221126804592"
      u8"1376740377577736438445048174094072843482730337372658453944087913253986"
      u8"6478668011238834906287570790674639185565008847306661087021179493235973"
      u8"4095611042301233818008337027956220500842787573600498082441490046795467"
      u8"8109542011365228560541824249182727007811185158985242211376273868673475"
      u8"7001540357800072027925544793796807288113906185008824090219530547511600"
      u8"9441663025541166391152390737291930982541896422115392340917010834477172"
      u8"4154529887865688661494566417112543862229272476650379214769303823638947"
      u8"9656278512543657402115463272875775916552209248119009928565922669715598"
      u8"7870969185016050940475877159093605731079395725105907950444568651539294"
      u8"9091283300668307176259717270365673498622038207509964660131164975660625"
      u8"3424151402863572341182129795396492211981573013262429591544771836585150"
      u8"0711774650163240484178164354940640244325806283467025945571208259703352"
      u8"6199392465935151058587440933230887437360328485106047564365899380787008"
      u8"5688783995931639334099563310830749942583239141371543577504761717404111"
      u8"8173464369830444786986056103141051046250956793824657564014182160361391"
      u8"8860393668003931552914758724747030288076313792630208773101956618515085"
      u8"6054576321674355075315335454148232875940533956420721982974114226168443"
      u8"4212226657506754780368087519518349273936954044397692189286264659920343"
      u8"1909368282130257542190045799666099534618688372426195437334934417902582"
      u8"8536431233800580321957619595536838712285755904896454966251453627038949"
      u8"7706570385130850671849923861278162598206549627254785775533010393026078"
      u8"3052405304635664440509072641470391824071948081778760835798964182260620"
      u8"5272734472417907063786226749492716217867423928204096229038450983750160"
      u8"5929054136383926737200669428620556722251792242441279406416129793817177"
      u8"7900147515040649035659425698181705166794120292595432726336671903494238"
      u8"3242713023462506360847932089765938005121834745119478108591190284778390"
      u8"2028100795398462874166656918697583240434437157855836944710037450050674"
      u8"9154805003368352300953858386992284050917384444362968320045395620073931"
      u8"6777461134067865788374160476390192165760989996686682828803998111435103"
      u8"3355775534648917632637278519094817361770233278918690237947458830543862"
      u8"3368014899975488356683153405814076175947577052121747026153915479061900"
      u8"2776886491250989349695013233174432297427085674072992872885500603907923"
      u8"7316165641988759788571045164734824621631736602193253576550576910268523"
      u8"7132639383019564068298302270831848064925425137476806266556010577009748"
      u8"1091614204191733076841563800664254189849484903305649446640282114966145"
      u8"1508352278502361422895245315889489845582386486068941567627634385169372"
      u8"2488932215419668222889748272489746454359776646948442211655531880728409"
      u8"6865645547725164180325631682938682126055969532039121472071710632511311"
      u8"1479966158005659488287656486469813613360938013737389541635635758015617"
      u8"2587465166438696590261119319968952395151765097666965885584186480935433"
      u8"1338975806429196256526726421757869093790577232445670469849557610618003"
      u8"8998487465070333593243737449194931873305994751890719471687022738909731"
      u8"2196483452576666698123502023881370887731086690561765491969112244447551"
      u8"6802319196764884132718229583756419522050500962313029216922750567809940"
      u8"5671812255689537756760496712539706996149638283782734203557505747699274"
      u8"5790776160817868620176035996725570242337780232088425481993615775705886"
      u8"3564204104217153522597919081928795327515402878473634279079482682160849"
      u8"1564465031142531757972529283592804347651282613711115800991269696487596"
      u8"9509540728566913870380190351777775776868825486574650037542793481198480"
      u8"7431556756611118137708084201964883700679764062938038796808151505846497"
      u8"2787623846435510614815418169690416256992713528447481721390662755654086"
      u8"8451755903793832988044279811741430445274430499831373616787995225230364"
      u8"0691768005459503487162468536775309961035281037027959687117578058850353"
      u8"5033011379649996979362134280725815674340891202047558658701567502159700"
      u8"7261806974162417752987761930524422393921620143592311957666272772010103"
      u8"8836611804977081945006690526554468409288562528169293722664045258153958"
      u8"3817621826997568386844830698147791078196824679260009832728550482258807"
      u8"2621216988156384163566609554520376035360639579371560995984407757757268"
      u8"3574486459148206318571523847402048789719461399331355516004072253331589"
      u8"1457978029783497539590367239717199529877843503999090304302782126405048"
      u8"5586803415161560542597884600205198238402281922066715032641561913076084"
      u8"0999926215810615510025310428784084513041380228739198968301289713439759"
      u8"3350762586570174018455463834357579748435693242252620652075317388036994"
      u8"9857882848367804838681436200075359042893524381112840662837757816173524"
      u8"1687110019641006531887748916123280881223810493580764862381937432020907"
      u8"4424737994089461849123366216677979447187003570157335601703003022292372"
      u8"7335228871746796292528771910550696005920560335087339781883824093127435"
      u8"1308879590595712334777140471633069880979642641401541431834408461097317"
      u8"6775622041076203831250379096462087308503248061031292801294039552365099"
      u8"3006945925480317749219383436489789897977407954276550463422534943928594"
      u8"1323727233464846946432652412749484376969273051300142150088289000372226"
      u8"8570362365309371646156895033059437521710967493439623977050394213001627"
      u8"1533051354480611774252787284421309397677235159140952364130279729361876"
      u8"7162476439196575151903960800484004465718772004429053159750226688553417"
      u8"7466658294802856887734338920913721256364459525282024802227484628369083"
      u8"5267512846778366168095465818305388755781290928167893239339397474121946"
      u8"1825441399748834105692501333070634587362314743428905104897873527326638"
      u8"2593983956251420748455571762392225479565562938397302371625149114547049"
      u8"6426495418824765304966595869849369776621166593261771920549006461667966"
      u8"4447741866893612212368496639441090068911892841021653207453483701569628"
      u8"2981689369958893807089850668126818452247209723232008990991016245796748"
      u8"8106746783153761015966302262083110171077621682131595200590791066839357"
      u8"1439860590381591397045170270933785955988727068312619104048291234059434"
      u8"7146047261253365787766272315673566344195437138383662230409138707005280"
      u8"8692606411531564786251514250237999716305951290782716624126958463105958"
      u8"2377013634899290456571037585725814917151699789558704975852402203856839"
      u8"6769816785023232392506838558671234301371090552593324561757096967944818"
      u8"9411663617989551350913631641609367469360204623010570352510151196954721"
      u8"9551873241938651421184496430350697819965710813970399577666811158357168"
      u8"4210282713776010575232514319863629796845351481499711129005628259002420"
      u8"2107705090964063962707003817281991316070371786278432369927136408346839"
      u8"0952432624475680839542197914951037659315201761657979501873661280473886"
      u8"2811988361899380163514737828958638712416305434508963200339612304159060"
      u8"0687191758484258419700101682848428897230351604074695467700768524021063"
      u8"1811219392080770475696021387984655002893781576089346511270195952320836"
      u8"0834779807814154946688764448059713314980047154803916581967834014035152"
      u8"4547743974438305419516899173321325104761536743188447684790517295873275"
      u8"7843840599687799427306571200430151975194153292752208501371627198210370"
      u8"8499983511342730399687454613907004650556081725790817487811277037456993"
      u8"7679875741228084120324044213088414467382079206545454771419599262449186"
      u8"1766040107259704433258654546528179211060159877766618304337299640988432"
      u8"7767059532001034716918733016612078373810893530524422821739938157648482"
      u8"7542383879419803447226394658812025534535558214526379073693543607635381"
      u8"8433463640162648964040545468697744068584209585190833527498318959911990"
      u8"3203013115307353394713484822640927724637727908359631214526498623720283"
      u8"6590429685990972986937061549651376271610829594184764644080258873673277"
      u8"7694760459128977498850827328945789776890894409253723592909199702285984"
      u8"4114383036063197986438731047377974593032883404765501779315703712784999"
      u8"1636728492204460613281008799483875014327920662449696910701327556191370"
      u8"2207464922758662952997104835264275055157571931537730200966298123999926"
      u8"6266509051559477070112542933907678740887263792038212431139814972055913"
      u8"0494133898497232897066227063018642445316950657909641314828214867778114"
      u8"8572927287241530477900419149357202939163831284577981284276827544619059"
      u8"2798583951332633735795922860579363000563026551535090751144390390071424"
      u8"8831285143290013470932077020780965901640394349523447955606360825550371"
      u8"8423748847240853757934527558299830726641161611483979171362546806447181"
      u8"5088509144338273955475611076519343591212019844820174727024360239889845"
      u8"4953923386958790172792806059747408061468556896146545466799219315097322"
      u8"9726215600423633691635536790353332260583397281161696454865534326916261"
      u8"2825072420463332950819176605003447401133586473512661710787844885460445"
      u8"9140033280464184194700791159175485627716919931236467256805861300894164"
      u8"7997755436780685341672567009151918957939028150923147891248657485366346"
      u8"9455528278202264681386057484464215448624732131879417718715299136646699"
      u8"0477344881651183399822295084084733430455222303562789645461747654228218"
      u8"9620586211406523384194303387261496554537391047119715407595432073711989"
      u8"1095850579955348766809943671921397048075546817634807491781220843541995"
      u8"7314399467482410948970408638013268798887604510655601930912601532224870"
      u8"5221743200283112866147773691385756833072115269409380005785815074435878"
      u8"0792146332629668064970589971210282985280648954061231261996043395544703"
      u8"3015891611858739162278172833002897016128662475012624298162515115080120"
      u8"2830859061466434271544691879835693140323825852940017791976098607485423"
      u8"8691364979246113551969495679410219938170921715202902769939814572633411"
      u8"7288188638435588120848821594582549879816296022694828952549747601004129"
      u8"8336686653362478634273962096982024316875779306161815220166344315162604"
      u8"0921364360407936839574426175336075309392724423727171794465683276321872"
      u8"1732273269755626996233257887095859644492014079376877830570209471665752"
      u8"5898394682197470187802804583183408838233569835011490385753345583372875"
      u8"5364083633891981935966837955073256287753700956001679468296037426636294"
      u8"0112667139146134732142928793366710877611556070082610743022131739757726"
      u8"8707536000492604652793571829287309128284654583301517763922967737057926"
      u8"5347155849489178578845072760773754833516066798017573274365916082796713"
      u8"8131331373464631789940216052080704168340464139875674701359853514082660"
      u8"5029706851204535854219339555977637602568895876377989425136283740773140"
      u8"4577677546031918658801962830300928623286559229129070296500268273608957"
      u8"8643077937693870887886607907290626419349470401608750510880426822459489"
      u8"3591750533457404306223781474815477063914532507585193854367437776590707"
      u8"9967261230001860500947415508759037130236296209545856726916469175122058"
      u8"5052873359143347664481769027621638039360073548690592321786101753080070"
      u8"2117248134080712701690132485872093135351406456072518001941952816143874"
      u8"0587150313885345327465185619980649246575800278198483470958243924606624"
      u8"0502384963461014474627781275604494645155052683387898125214313565238751"
      u8"4686109649058332945883138523136813104741909204051148883125669147973151"
      u8"8515087510747453642775829000675249312978126186922194252670232211457226"
      u8"1255753506128799598334528258019181775923491424491237750925273998808243"
      u8"8338414589772785209863302232988354112461308475976839899703844607793940"
      u8"5904906914031539370625627478656048530581273757445836479872273122442809"
      u8"8742958439276143642277392108345885240230621985165594252415210837497643"
      u8"0849196208411906967676218239351542171782630783541231182777726956870640"
      u8"6351019690803902680992099600745152760942960857624915112167897388528245"
      u8"7454854354939663138919872097839114292984553081523542360317399435464834"
      u8"9071709194611922499119170870130656226806087342867788198772016098006434"
      u8"1653568625286372743153785649388335005590392878366942529239343131891098"
      u8"0625827914766153550342150855161362195399097296315973686038146474539708"
      u8"1701465386427901873782964564322262103086918226829512645759890938669394"
      u8"2605922996114425189118606891628362257576231073688039777139482212720288"
      u8"3345217168669327718844430961989136640937080665260098168876141300354417"
      u8"6851633038325127413342072194089757467256549484646194225224545047671287"
      u8"6444616328912338705904012043554116515228308576386059526291823238814262"
      u8"0913169553527358722612489319030058436860646449143313043638942224213318"
      u8"0810264749264047894770939027138558491175256777985417803699182804007255"
      u8"4221978954848380667865473619795336327917660759065344681728422879928825"
      u8"4123964792718521230256351854818557915363837962049032563813874844751564"
      u8"3584911331884378045365431466298248545460420859285221569880857880908284"
      u8"9478530815667921037863677772527344840535368983967465507600748550441330"
      u8"7309726430916703696108973165429018147134019391861175642841564697866269"
      u8"2222597327466111292224607740064737096264215969946993486884367948707075"
      u8"1132500115286036920752955151691913870548550643599922446326189826466369"
      u8"6782978828228401268820963206349266420163878446900668650238821420759147"
      u8"7349606610241660099024700466702200076410168599239073059486490549920646"
      u8"0223536295453492295261226559435660758784624238287238555235537605980392"
      u8"9814620784725044396329788823200556015921488267767149460283271110972986"
      u8"1650858092525531758150166222257209628770455919971514715477434766044996"
      u8"5855210336470363291308778268734926557731391182020688080326347829625221"
      u8"2972772153536825038423339596903877294138528643790531293056010321777729"
      u8"0209188394500430388750208143231871779299275114237425786690075600291657"
      u8"2771224832442987168337156283406877314315808052244562182531068824770808"
      u8"3070754565911322133124871207653927105737325875684812008489863637078634"
      u8"3663736987228676125621929435107525479301440551844691009641556991242586"
      u8"1157687227262982133312549372187413656666516440599510971723492256880584"
      u8"0817007314428176196640777934786890480695158756094593249143236662124408"
      u8"6813814319279809114864369814528004967820058347785231081476814410793181"
      u8"9463923480807885590636450732303093156734417931140131008714404484528011"
      u8"3388518760809464626157155872347583198118408773008259523899764921339964"
      u8"5125167301020376834761466331799136475836265630009821987110058909380474"
      u8"3051011328991914407482384879248039872144287955691916137867571651402462"
      u8"6867845958146354924607194634250818226180336971235287617235121053142668"
      u8"1571512336361785016761975837301468496723839612398687814296552100453272"
      u8"2807113311303344217281926640719086882221672195837722423394463414040503"
      u8"9572641474321962167547119272098544149446364885425989409224659661838754"
      u8"1006426078996108568405483954579215298802259777939538424901481294411267"
      u8"3196349110891777281465775715887001917279935892139793071315413061881630"
      u8"1243908147654392654676062483976753534280569750815423008630468967283455"
      u8"8492188951025475241281973776369928113640972468103143387642822230254834"
      u8"6186129455930968084350092902352056598709383665479205880499805757916267"
      u8"9724200118087590795211959123122712044574406199469572372952444834547512"
      u8"8420700044976193403308767101062641811247491861131080295141166707768083"
      u8"3145806217861647014754895003341334532458223315379579664154310013035823"
      u8"1665162768444147169946161154821421424729049320904043587578617766678883"
      u8"5513638366665357071756633884926024262521759913269187695369606558161658"
      u8"3315507942013267161038416852110674743723649307265943263633198966204395"
      u8"6520094954587789059053306057630018495887868792994641133498246280091767"
      u8"8725724997107955337058709562821968523806402186618681941493102645425120"
      u8"0946479628123243884647823665633729483483349134750219840591410684665737"
      u8"2419942454424700726482282517345349404809727184920611005222604404951701"
      u8"3303111087143415839457579375857766352632921805427163392832905069943343"
      u8"6606703027954487776430963437531318999919176576064837344844510107535769"
      u8"8386576578770559814548907984924752344749794758078624996671026949809385"
      u8"0356417004482469499503253134875424172450454728330239477046749621108500"
      u8"7775556164784548165729478681415766375792879429420318718097149970643092"
      u8"3503367813617826350355121102850994342057391054002217289495817384641135"
      u8"0875193065696705195918592774367598223030648339993498602126538205099170"
      u8"2821928566251815348582742843184409305211444415272031778518304590227706"
      u8"2723471475084239975725077673159549387727309853563251668728834753796997"
      u8"2027770046635113826944401179170858648203884614015852560645869304726601"
      u8"9769366815755295630371774277103650210855715325476996202163756513624926"
      u8"0707745587763993557315697124260749376922129933017828810768859002152114"
      u8"3802389369249966994155773076788660821144606142513568732357585339322285"
      u8"3397799113334356611270961887786060566818574493442897540306531130048640"
      u8"6492552090420031806911658584987749268896339039076303139392892600561640"
      u8"7924593733766834989734031702398464134472500041529279011568939034544256"
      u8"9725113847334752668532590073148219325919177783749764592408057266043863"
      u8"4443444627727939992119332671223707290880855935737940219202207839025475"
      u8"2135507566092821538218637893894601073214816102373288718768571080732912"
      u8"7760274899529543350520340546204074159698697143093668216910772224054627"
      u8"4894314913831730688417260538984721522858355009461354184641611340979718"
      u8"6520402145964796485089406600764496556304281362027563799361142399478023"
      u8"6067625323245102122935402609953709581396335115938102734287192805472489"
      u8"1691630426631916814813662764756763225948825196667756269231708015676994"
      u8"6265075995600144897200954610907001835899521328688550764943431390351331"
      u8"9494149045034633861643875080207011767352111416350192554204936792186921"
      u8"9234266144247830108859904548388140888969393087849046408500380639710316"
      u8"1044413359747886803264343100800660725569040417172390626076556406509436"
      u8"9491103569744537007898841169531298875998093307640034265962094927845461"
      u8"2619403390749626150132688910794242605297392910658095754445814178315231"
      u8"0410220317262854788341628086636185900633679791278466134681564077032834"
      u8"8816612874736907860740449015616292961780822585446041555741877287255709"
      u8"3824734338212841757990492840606706332120852661922925763198457636394873"
      u8"2871531112286173063776462151752248871601484579715153853078239931931208"
      u8"0658816431979541340391521801661357770009476978097396952352249526822795"
      u8"7448387771933458896383762096592784577977864284731363676519557174560483"
      u8"8520568672841892571709052855150502964447134705814383055626787133994876"
      u8"5368484056825235049585741167132981551040507915292239933788989601493937"
      u8"6835981306680276495846401828614665442547817087843821375664335718900140"
      u8"8085052002886178110825523162208027240436457023395959155355534722885541"
      u8"4800821891385879006258464407111218447611641564637338473073467767209347"
      u8"1296436702634427886878586371681048208444174554105212451697241951771262"
      u8"2145337735506243819815922129636900360235697701321008181281963667770462"
      u8"6891945554820110843746168512203973966391401119130678932020977397706042"
      u8"3118727497447486316443033160072706439540745907414293203373067682584708"
      u8"5068121601432940773691561098094213459067543748973387538663444664440195"
      u8"0167267398861318862172966090742695107700018438167421100108048635118758"
      u8"8378878670016469510490084480526527113836251926282947192593457965017221"
      u8"1461037641916641369828189753854940899079688866702765471993093164875000"
      u8"5056284587742252803566105027892168346324303683053290222443989015212911"
      u8"9685039532066094216066107087036867149955245653953145978161694708963884"
      u8"1579143200277495528207746108053377180306531192412823380884694616356670"
      u8"2357364063766107058696954902352439059773363005940965070843470032771798"
      u8"0006166242591026311048482117049721617935676782759467336254552215552102"
      u8"3949274955672149546768840337384529079433558308604886709393479504828694"
      u8"9956797836019418862727625308858605499595399806772984253099784803455472"
      u8"2076898779435746438122234238023661641883793649371142635287675435689469"
      u8"4970160464252012849355279147988149499970986502406635748711952925409874"
      u8"7925206661458677724026885096391893022722252324764994726624014955499659"
      u8"4361449342197547853933750908784883520547947308349220283502072299262622"
      u8"5811731208331493163698574893950348747531412233221907761370663618230283"
      u8"0795424681803661357969693279584507765560763314866835712644764531749417"
      u8"0079271603319665916894410341068524481633302686908843997849333449329734"
      u8"1983624376095496027400788179001146259757124802430806952733520313569774"
      u8"1499217567721741444006352406825868504149393797205545393346538558704670"
      u8"4048341691731134629780974326416371046521907214688430304763891200010522"
      u8"6567688563397686808211252056530671435719277752857390398091048629672015"
      u8"7301984979321036822016937635214356508915659263495305239624346432204757"
      u8"6175828230619789185277413101517262824403375206754912633502810045010187"
      u8"9577522572684185968015650514881908971995822940026699033806600817422071"
      u8"4708091523602831877742111158757782374708756197060863917285277609047637"
      u8"8002672040609258780340293601771816326393865780072460973274355829111256"
      u8"6382384844846922232631556283896817644069408353117371763136133456955327"
      u8"6731466802015330853087387753677612477535922466640362514402901802732229"
      u8"1503622513589154610399376406181222764337683538225458783222006771188233"
      u8"3621581413665752195693403244094181243691722669002059328084553240307791"
      u8"3776454624438933530985263814690938958440044869130159680587533711403082"
      u8"3861224205430425602683461418887351557828224860058662692133630423755067"
      u8"8457484311301593931835049156795009156666484407703670920107429134208710"
      u8"9357786703025921164887503887464906069870715755692318142687743277590843"
      u8"2547779406140315460972373981244006811808686173733118489718771785067314"
      u8"2406819054956759569959219399415071714013981886622765945627488640903825"
      u8"6976767297630605106995610347577275242321104072316481672562515336668347"
      u8"1183137013325143540005080335603972872700066185087764135147258432523113"
      u8"1545758792898492468397684117457515945415947876787520014970733368301220"
      u8"2685666695388889179565762545447883154467299033258103119076310942352436"
      u8"3690967553135933941857973053098633985423864691718867285984675985844538"
      u8"6544288275891683237163388686648000963179436751229684175162320141813860"
      u8"4181456528922216153496377566190156902010951598699136334004493752652069"
      u8"9373783243149763665276900786583089550804880068689678289866184112255389"
      u8"3197439532869270251287210347524062277481751084494672600802836535815423"
      u8"6814331373882701044502166403402429870346837100882176962467259900712985"
      u8"9840180863794559308139549728528441659794766746608374900355616925485728"
      u8"5209652242493741999840557395530257711769889304652496149104315705211435"
      u8"6531891987480698744109420882181937729807332005577673000220470405581893"
      u8"3137884740759172181840370280327693450545750120726736480683784283744529"
      u8"4460977158791647665485673336691083423628821814109085542393727968267951"
      u8"5210751451966090939131755419917724910810842480750411759301097601432740"
      u8"5905668206905083862805075246903591976160205069226664732029236981536871"
      u8"9264036321540010502263375373155622442639400180407521288086183673136058"
      u8"8032655606336754236796781515098246809422248526748911962001488913344618"
      u8"7507878727770664418473790861342291966958256625125691771719352015062158"
      u8"7977796768800807018336564280483407043808613687926344019542357128183447"
      u8"1930142345411030071574225634725595178620149137569761799054170486963066"
      u8"8665643889585067966729729948103363814803070001026815260380525369580261"
      u8"5087540207766923682105489985502871970843569819748169358004939491698837"
      u8"3209671917001080938508586021814758676459011383299140933687860868803419"
      u8"9806539034747368139650513801371790678460317086780589902323762785255118"
      u8"8577173028849424941659660067114437128875996573937362274222725245805772"
      u8"4038383971860012823873386856209179267792489609826607495007379679782657"
      u8"6799978026315485744821967382233554851879545131377561670294256043938049"
      u8"9480945962171765711498037877165255664814853531178747023263736173024882"
      u8"5647892895413732783513584997270769630955173116468400056562954052571053"
      u8"8522539081128534788596259776311428352527649520222970041733254993636642"
      u8"0918043305144506677515989532714442745324386709967385576401603181677041"
      u8"2297550383907137413140208761274105472229418925103132619458602836000581"
      u8"1788270559559803916711591108826938808365550485977380935927609845385386"
      u8"8572397370716132824805263406212073561811043884565082481100873393006872"
      u8"5205254240850390818702077926596729320079570342038379290013005978414647"
      u8"3155055240151953213706496022941932014373705534272887619237658486937678"
      u8"2143863415862552219384241520632882460747317600934511124873995548087806"
      u8"6400612238060106530657115713746963380712435265804846066142306074545236"
      u8"7112343086492385933479334641531488386028880567934946016624659630493240"
      u8"1348936109698849770969788079292641968799099453169225239170416407428203"
      u8"4593422990501199436140477036176755277028675072126647895079885607185577"
      u8"8648052653268548013811183939245579796895402607616505822271457408332020"
      u8"6630905252452015362780467839397955760840915399391826425082095096827281"
      u8"3116920294202379530587511577115527488554710348199680907248031487588848"
      u8"7549005681308917147649312951439283570161656647225229948644513278924557"
      u8"3778033415657338036915921420517349719016974512586365190039048755164478"
      u8"9644875193723390193118019768029254159957256448579704068058624979370522"
      u8"8748712577370830226581755703939781640555615570763460014895519133509651"
      u8"3732237202053923822769303726416911790121739117343911349798290656664072"
      u8"0510124874782263457441470283385755106220847395359103935145922890885495"
      u8"9955438421415699878688122379851950053938340919134502362173139100297060"
      u8"8178703464568098785198960089657640318696978741902021175436123710402771"
      u8"6654851775123254237352231883866000454955750297985832013400774354997111"
      u8"4377509469909108014425333487506998399336777959791989800312731795564146"
      u8"9608881125067858776168495016235657103307861496388956018558281273720370"
      u8"0075008212019817446335687523276854293136602779547560707727438928936384"
      u8"0930237699084570762705582904467727789111329128396712054346632195832752"
      u8"0608500407837247972787663315563653204948846738202807073830150063036952"
      u8"3562699752726335786110532821971560490681650854817500430888498762334355"
      u8"0862864336268745546236174724363088311478531713312331027491553334518144"
      u8"7448769276106014112779898467118636153093621368816811942477638116567299"
      u8"5396897852317708960550516393912607291644087059292206395342507100498889"
      u8"8004809751269165032897654795729278776502018094903648624769819443512148"
      u8"5625211211150886073902917252125314132258512499807726195925045825537837"
      u8"6242297293819230323650999540568323079444766419681342146936050910150061"
      u8"4296336927866549305577590641021541310809414781843826138057700927648714"
      u8"4912719023920607278207803671264548766169509068157779734046748586300298"
      u8"6122823211848265242587816677174496258650206701501625942538474849573838"
      u8"3536074865697696171644639214833212114847511236342481973065118947878195"
      u8"4568414959691753585499386602826450342656886639176030105822539227412698"
      u8"2204745340130246252486693329477924483480003904462649168269646327291964"
      u8"0263298721627463571996536519895060285152844803336424515625409458494742"
      u8"4081486408989132236535356984369896461697899573576029796173809189645640"
      u8"2616863721980086807385540571246502010768891677407343859276190018361060"
      u8"7926028386596282659497129410359349202329694232894433686001660644573303"
      u8"4682363922933864321705261928516584169248984576362874354533338019074527"
      u8"4030020762157298119559286699109379102121557597489116063314371195236899"
      u8"7146279715124957182669137279861017677090719898675890282742396055497008"
      u8"1403397677436265227166943064332417581449964346820885950460328857871549"
      u8"2418901807680629572347684493876988932892044423105498666191977120911496"
      u8"7788861287818053509889571932871308828680993970203419420666913482635942"
      u8"6255068712748576240188279709251080079027782491534494106618765741942875"
      u8"8173639901087498255421283000408554180119116888049718871424556110800869"
      u8"9752606324047067992118058660684639771654374781087039539752422645835276"
      u8"3149760712169863940446342508381645848955091069064585357304924493696603"
      u8"6388297937396051814930823465912651170695056695684354705423095352361101"
      u8"7265581722416262285461122633955968814999814140322122017609765207959036"
      u8"2557579884912517611924327255896490344921244779799524502274839244914040"
      u8"0999893327138362946930129079489843914654316839228169929031059034459343"
      u8"1062437384221975026324414203356640860074038381669136225953316785049268"
      u8"0375012251411462561656636381779422624167311994864281303970510503825222"
      u8"1324582851289320842433595903946946021833586747115399461991296343323607"
      u8"3119235118635641563978529027879240875343873200599148385197258975514606"
      u8"9162135305172010902813231840083315606199810366920797219882512716704345"
      u8"8586639267911696352127693613084814542985336759732579984812603403661386"
      u8"8765127858924513895220449084869614837621690899401353474072922532761311"
      u8"3843914473164220237951698934425425073412048445018109747291182559074287"
      u8"9346300651233305792458155938752121281687447651698450240049324608599262"
      u8"3757843330463640254787700542520193357977977160428161146201151476753920"
      u8"3341902814589757757509918202115711716548171942076395786465688562351740"
      u8"9407756431783765369213648209359803836169478233492553954392039363495017"
      u8"3102329457581959041899848704832518934249680447262890699937313068690909"
      u8"2860219727865756950623888139004279450773174753339904603441590930611220"
      u8"0556454310531957111865376892847710377288129969695599622844850900523647"
      u8"1251065655857627818407955520347423057257521728760711440340255744100048"
      u8"6295902352990375614540929626974903045772613153708976937640923013783148"
      u8"6296794761906697355952174600587767771045202432553602654291508805511607"
      u8"2166957110196706841975714738593143410799327095045261145886586991327642"
      u8"0202482581516228715176351931180924749540332040962454968045924163081408"
      u8"9480157002845400379258032868282906381339868936136227797595403805737110"
      u8"9995470581818948701590601977689512898597083875448596254944259567732256"
      u8"1974777130033788656706044777830313628648473374128180246591945373204857"
      u8"9319565172145226525584746828228280152224288837931818707589264181208164"
      u8"2837389428836448978751443469259609932367712726934705680030882325590543"
      u8"5531466521486921015841435043659182443086639014344966919575663543831587"
      u8"1715070820030683860411696777636958423467961955220258864409260494705277"
      u8"1022390524131720726193420143589502028290519477287218866180101991650787"
      u8"6529172040048781830212152078162364660909635524763984887303704824018098"
      u8"5815976887256045280830425125639237190506705904164290782682662088899576"
      u8"5872766126522142658316860174896411355015022811321685482895884343174099"
      u8"0084282470549200034950857133264593550897760241374783978754743713138025"
      u8"5111018033572990667311069251960073469756894113570940457678609590673721"
      u8"8732540252172427735336710289441742800847843454050372989533518454402134"
      u8"8535152501414884971371490118723594704430646064015656709145414245874690"
      u8"0724034363400740630956017678360258998541487458402913180201201315448526"
      u8"0128899611339351404840913148080450568011497610526876713386820536302317"
      u8"4961772201994044510108164442938361660076053351685072320548340905344814"
      u8"1104402883919798035784683065276478491282414265252659719473334919669084"
      u8"2696296072482885727534473424134222576730928366239199333901394757104024"
      u8"4389203073511899504430713624670821132439145578100893601933965727484049"
      u8"2876428784706318106573680539584276009573650392629516076089664750417738"
      u8"8538151851448241999985814765744716264243033310871609007333299208556097"
      u8"5769252709971589103230273460312986218448508451644330813492950735316353"
      u8"2156156536252853572465536206083228382857989900425979654028338377465859"
      u8"5518778556619900754413399563496033794006445090490170977578032514670701"
      u8"3869203018180941026139974806749568247249560648739103379234232761599039"
      u8"6522420198369967707450880796622141425221786388061231289783035292319012"
      u8"3992405352282997656571288413081543009213444847792932593873494840392783"
      u8"9475229170008554910903870846065843075759549070982234785884519576425854"
      u8"5757341117461594483989179570978768139132333271923093927325359381901082"
      u8"9871480520197499347319562680365717646535578927830098480014467418812107"
      u8"9329784187281883019811519527644261664676711739850798993856227735708832"
      u8"9833198546469416651649924264843246980939862907906237884149065279549617"
      u8"7747213392011014509030142939219285734346078984581292038163415394286113"
      u8"5791138357319421211191946718415822151974738761619158135800077465590743"
      u8"1069275804580913394237456006750601533021095229576760739034702967880646"
      u8"4148205690865100833080566352185756140286828056993922506765708455059748"
      u8"6556090636366096424949241290007169365460524655802058967395930410882989"
      u8"7654845777835922898061594422135859874095297641136266509167424361517533"
      u8"4672821311188953435836872956250684450151630629482328313267710320398357"
      u8"0353462484393781094897517465605964825187553124024619494596640136458769"
      u8"6319585692407898536780686164418051581455533710938009304525437131499759"
      u8"6183522688310932686652092957727850352484892664957960516851105224792080"
      u8"8860260408785740220405419798229106247354005193049584009703867403817932"
      u8"4468903594702011544657062152503361138552941171566744519766471276133493"
      u8"5431000645156371523027906337088388640477441291034000795403003095060196"
      u8"9310012126936788863378365640639283928114076709901724160566463409849272"
      u8"7860947685240410862748009834100219862340753298111170392333599208931274"
      u8"8928376290935147154062911311545183489938010011018336812371863346507374"
      u8"4448711161768895931269485473349566484800969752496068940502672559318261"
      u8"1168999751921042762495153972371565895666142022331384450733341417828065"
      u8"3351537305749198669933558839355144115834227752227961888643185977491448"
      u8"5713917490656178476740049648528656546420289498746982052247460645408485"
      u8"7782677683445840042218831297725714446549628524852261137786463949780915"
      u8"8395957242739739741228632394449605730850421812461615746320360870708500"
      u8"2323106207395738370097591833445285837614812671328426270100288439029453"
      u8"1034761234576103854924508271211516380944598830259990509137928004136119"
      u8"2719243106114703673431940964147083999811062836414815180291424011383573"
      u8"2918897009220819391433077726860040552028639299994872199137408631840002"
      u8"6597414757546138942317684419711602489575000550004192050499178905260444"
      u8"1559090922242152099483786266829485209108869987648813420724986606999357"
      u8"0558619577658445768150612058243741145989807275512418043235411259415418"
      u8"9051593832894808121606284516853844887692488208518668975797055328839919"
      u8"8487581091059845762302582848014122529649272352696887677485459121100625"
      u8"9039702084952209203431743176653243733034063201380085005413116650897517"
      u8"2214355411314196172917164962198142579724855476665269339337258006771517"
      u8"2022873259478555658367024244772064534742923690006238051969855002520603"
      u8"3186738082482040624681907555823468243163042855114507262694616358303872"
      u8"9380789385920251268587954310741809234300564476689983267320705625924782"
      u8"5387472354019189718551610110667413837995104360536280265347056498515968"
      u8"9530171455904023364267139248643348656829718970302582965762809652748005"
      u8"2652951688660874599782823714575551730474061863360972838565443573577668"
      u8"1137830415781653775088669170832833548676918625488884499715510794029150"
      u8"2478723769769365807010525204913042235825480185212994801550888518209227"
      u8"1693319452763802335199851849601589703257375162983146997757208480768332"
      u8"5393281106038079663614165129290165965879833547145578549865980806684136"
      u8"1037980948814347178350471383998057590337843104500505868944113389934765"
      u8"1486560708538825779170122232445406161391956621860233882612061385970784"
      u8"3677086319305428213449759742186406595853653940537337836181215645710319"
      u8"3334461811879413136458925268094835065138424958543323679025285942971948"
      u8"1311768742391043385522860296917566112898818065149477948014298804445301"
      u8"1599196082014459349295739487539180746338910581917506684126196156797499"
      u8"2864805591509099058758640870116872925370952233187519890355486449826828"
      u8"7081892433829016524282325181043465711082144214035336983868649665313501"
      u8"0599328716721979747864491341859296083119182348580674250549019852572208"
      u8"0969272295554303502994593578178758147879447950764041744951548379796546"
      u8"5865519667523121949634461184235189674349032051280697733971004180776307"
      u8"7032672309652355354337150853015355256184458895382988493250098769191993"
      u8"8100043355072363954526246969357503706346640925693684444835471823443968"
      u8"8620859873844999362410310984873731830674810118842841296218765992434697"
      u8"0647477908216006231814557785991130771310584147985800972371634656046319"
      u8"6774891740475049151701817454533652947716537922784739095841823056794010"
      u8"9448229710499984072045466447492635230156270059542794544514687495422366"
      u8"7033734949415465658580248408157240516229936491928294973094757014772657"
      u8"8283219405098013912379148722217960743783064205906709366393190956275906"
      u8"4557879480675139435744508909274304942065201651994663578721458936495038"
      u8"7597506608185084880502742009337701209799828215925994566585530570514366"
      u8"1633694877144470054064646283372758064698245390912658992609975438918093"
      u8"7517500979413735883795895862692734791388867612712012993774097524370041"
      u8"2696248724386103472991524658169620603793792139779480339564791006823381"
      u8"1491571074382488505043271790489766506331204043869325491022121781131766"
      u8"6329505860399639558149996202294202175412081336543803059640664434246302"
      u8"0733459517380432200746266370363031923020811936354143807814042951909404"
      u8"0396877098410269777145887474297442078713304007341898444641994957524696"
      u8"2092081402769252045367899684049592664903259242089277551105969335367734"
      u8"4309219385398407292956000313286567743314318771900723318296385706843035"
      u8"3719076677296434151734255365593430930199401866066256537048987822313923"
      u8"6886637983685921351171063847486962136980450750652168008445921373531781"
      u8"3082616315464167369789393615193750994138643921229002261248141137046530"
      u8"7894203511811610112887808828806298802165712399964307636042885662460284"
      u8"7578098974910779007235008206116789217440080816364041557305390299476674"
      u8"5000521746274041494637290183706490373734410125032790719710131887193312"
      u8"3682563294642404873107540055790671171517772099194503074655384246533013"
      u8"9098706387987083108994688277550097299021119834804505662240370274479024"
      u8"4798547518613754035981325805517712412689815136292514523989375695149762"
      u8"4926898978559322295068292765494135082999749270992782571053570261196484"
      u8"2109527221780111779019955325895843666033072002060978776512832914165148"
      u8"7791121670513486001941445318506444409882604581879772961886796313252996"
      u8"9842671846196586403882714921450920441824425655914587101011694474794122"
      u8"2753655746717740902627286073355597724016625212251675737806606154706308"
      u8"2223604706529398095471771002753270365474480096290839576541223135588652"
      u8"6268143074030240738581407881094254212928785245490782430175269035907386"
      u8"6124783950095653306804691807305510551302976398994980588630168808148770"
      u8"4574557851747569150743079222476217185431861236391905146540687536294999"
      u8"5923760250633706518173423051306529665434146563959880101699552693197218"
      u8"9267307821360398523621631059288274432813993887257805124448571455404103"
      u8"1783202812394679593860180815689961756514397406264059247674414088829266"
      u8"3135211157527057300490682103625333228176502632898099473678291655029424"
      u8"5295028415117003528533713365403602855181131559392785186883899852548812"
      u8"7328709355546003895799861798219610051843447491910824152825630177483123"
      u8"2993782001423720644322222534251060279199536765056898908348650305605302"
      u8"9415091987986541051071302650966368407822634670691620900331078959491224"
      u8"0919587678598533880520231836365806254205085980932362795166575458522951"
      u8"7244299936430498988367214702964558420643040885766782079862536816403550"
      u8"2113457857410258796122282767464328960807607346528490280045803632123618"
      u8"7306488361284992527108852759299105056333802460537848608195277588666290"
      u8"2306956263108835642569685312282511282732891435622933576696971964096209"
      u8"5430380359145532268641412961261381232027649926925992350484128978500170"
      u8"3607661967642958585094771559371427298049488106843394764264295269117245"
      u8"7562285527044730795344858425597290243892812777317480284908048864156858"
      u8"6557376759226941124558274366365369864620485406544799379347325330281045"
      u8"7161338154881275418830701113707441941309343407121086048954088775543074"
      u8"1184394507867242206685948598609666671771233674349012114211226255132202"
      u8"8938924806233962938084034186387581824843625324074960538437744276685732"
      u8"2670613462663222418864821494716939945155301543052026303539117508156515"
      u8"0325969994311124691777659519208913932487475427440655612609235677897705"
      u8"8089487255773043802109660169202148210634040071733805983332332897915233"
      u8"3503366806265568416660330690473442197797533758285729616602278538965293"
      u8"3533392994767156728493473837824810929653320925739394511431633914487842"
      u8"4709233836342453225034254551588123535000949614723261051101377916484753"
      u8"3116059633062411387953531520898895361263625056607049199230826973493350"
      u8"0031318145190538897828744382765936497342906083936918976189283067152802"
      u8"1766956291685165941397985253177092266117230681555126880153882607727607"
      u8"7889420149878608570396170816206106042961313477792115042821956594366586"
      u8"1250627540108090269020897360101730006304530776134236889334211395597678"
      u8"0351394687330815578992668484033475279540924846109740213301913753523130"
      u8"7367869704007346925218408233039985394612091746756478899943995036948832"
      u8"4036840446422582065314351040700234459779837624527096834100050359969057"
      u8"7248554897406080453636767114354174117002363046597144586917113616755924"
      u8"9190544406418937445020212273799819876462573006658675775505847706615020"
      u8"5729555042661850869500133115544467730225304994863749595781842040450263"
      u8"9473675811624550314973100658338042602475768493674996720211781976263587"
      u8"4715959976076009237800338240038540566809661851068651976392194701113953"
      u8"1217626607703053746259733436022991904065919631762900281778477756206028"
      u8"7303272872912696033703016311789413316611987850377480238539728727672579"
      u8"7161744273745462933029147303589161353931709164855460896948325140819586"
      u8"8234981680116460469685412060360949492101663612732639297465990417787423"
      u8"4534954614589134888668738506993141897061029311068923928256855750625274"
      u8"7687960287451058560226449747897223666365703531620454049862223794598423"
      u8"0023837419658008823369602062032542003821471384704567574442844073958630"
      u8"0861454667106539935417713141629860522997735993326416839201291738532897"
      u8"9999356559335083230811407467143224676450338302047585831532696650212437"
      u8"4370389603231978800938540934894421496459742217415797929899731662116562"
      u8"6512151528149599135532313997976987493674301915810273363523470482271614"
      u8"2100198943435025644627342154443837960519229515179150629228049908216775"
      u8"9212624303144181858255170065625230401251127180085052451598742249327251"
      u8"4055469931638328564641882690676700782276409483301180562664762582236508"
      u8"9557026339666347341286368381465985271994569511088828913211213468176555"
      u8"8666883156212711229828333044546486177416893689062117496011196103851808"
      u8"7175848376862528479294837421194250307095241460823977727538658938663921"
      u8"7095597095858819218654627022507204086098568670735296725076624011655977"
      u8"6844974667076901281584880336755722557824769021928156062324355358754920"
      u8"9002692581003696603051220330577960098025472902906348851560543937657371"
      u8"1973246509249607630016531539185198344999985672888769136590483138446579"
      u8"1280838746130286169425853300078027692590777357267160214860681400398589"
      u8"5124895757160221306139598175916972592299543585472891227371007530955265"
      u8"9225314672671708683179589858909558940673295518383284102093662277632144"
      u8"7814354248190120732768381598105867180699447334817221088022566088960711"
      u8"4719538559374875857156543049830917635079893392267991194939219181072232"
      u8"2648269820271573262190714455667176632003281560913764042139689954105912"
      u8"9078374387709484587360493856168524673389515838120823544455993341135409"
      u8"7121840630465165057080880353962654448030068417087844423627678831174716"
      u8"8206246485976177681366662155771198021020182351493413185467087105278153"
      u8"7983885474979695019874082055087312367232296564848966486864589852429854"
      u8"0270002598540763909114986491544551550237748757063755655176376285845510"
      u8"9616891915843926835519485317585646646474334039454769736718779478261132"
      u8"7378914997516658915474075223414341081579711288141279216851332403852693"
      u8"9238961591526290190236386277481679122967942464942610551259554574524090"
      u8"0958140655774780797752889988853495837208281892489606230922614800280524"
      u8"3931667112257430582639089556605467599251180676605796751015418385798333"
      u8"9320822480790804210784253963784564773384315664115737319190407197409970"
      u8"8443375891441252695591511895712098259942433262329439143517084625366744"
      u8"8845397798922999317297429134933308044882298490672969070605600720831389"
      u8"4245509775946817487765604580896280930854949582425439549916032845529992"
      u8"3162205388127697170587651234356923971467728467911324438481944746294554"
      u8"1150845532181693010145622214573421902160282420111964621354353918902903"
      u8"8601750253330796544118611896095815815025020545030805744974939102757059"
      u8"1454846626363361220703825308888039688497958353834403452893369891431205"
      u8"7992038698178313962526336219391483194180274667413203648922538360698525"
      u8"3316420158580433529955625299872038317726437518863666662280160301195180"
      u8"6546555711895348252586528393619850923657265116480081573599212815625307"
      u8"4528032864573252773388973526982447850864902741127457198013497611161936"
      u8"4099089817349638013063690502888186603601696989500503796032275303348816"
      u8"0502228372911679878422049054734937543243701291073860299554390166934379"
      u8"5820479477752099919347161639605899176856894551683224639077847926456376"
      u8"7388493976927687983674478712060490448893929893819750756564230260542259"
      u8"6588741652933215317147252796736175192467201152593908749733362580631432"
      u8"3600494326991309375285452497840385487348069574473686253683481517655541"
      u8"9393164542316560782359719171553416127808831409573243937032174543359786"
      u8"1664617060346644890591292540500512652245509189351529063866915402499610"
      u8"7798168143995206306455623935543597086853717257630603962395476042419970"
      u8"6310055677229199461718343871726248114549151812501303953934324870996587"
      u8"2268002989708309744947981039318840643586305672560037207224891801858637"
      u8"4151874433387064804773958479711152820275199561211719525702307012174464"
      u8"2961503659066241492789827333155032115257900045722291980860390410868656"
      u8"840331387312722149376";
  auto large_number = tc.root.add_root(bigint(1) << 224000);
  b = tc.root.replace_root(b, parse_bigint_decimal(large_number_decimal));
  EXPECT_EQ(*b, *large_number);
}  // NOLINT(readability/fn_size)

}  // namespace emil::testing
