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
#include <stdexcept>
#include <tuple>

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

}  // namespace emil::testing
