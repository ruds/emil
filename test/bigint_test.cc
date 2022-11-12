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

#include <limits>

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

}  // namespace emil::testing
