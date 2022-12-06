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
  auto b = tc.root.add_root(parse_bigint_binary("0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::size(*b), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary("-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::size(*b), 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary("1"));
  EXPECT_EQ(*b, 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary("-1"));
  EXPECT_EQ(*b, -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary("00001"));
  EXPECT_EQ(*b, 1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_binary("-00001"));
  EXPECT_EQ(*b, -1);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(
          "1111111011011100101110101001100001110110010101000011001000010000"));
  EXPECT_EQ(b->to_string(), "FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(
          "-1111111011011100101110101001100001110110010101000011001000010000"));
  EXPECT_EQ(b->to_string(), "-FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b, parse_bigint_binary("0000001111111011011100101110101001100001110110010"
                             "101000011001000010000"));
  EXPECT_EQ(b->to_string(), "FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b, parse_bigint_binary("-000000111111101101110010111010100110000111011001"
                             "0101000011001000010000"));
  EXPECT_EQ(b->to_string(), "-FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(
      b,
      parse_bigint_binary(
          "11111111011011100101110101001100001110110010101000011001000010000"));
  EXPECT_EQ(b->to_string(), "1FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_binary("-111111110110111001011101010011000011101100101010"
                             "00011001000010000"));
  EXPECT_EQ(b->to_string(), "-1FEDCBA9876543210");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  EXPECT_THROW(b = parse_bigint_binary(""), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary("-"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary("--0"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary("0-0"), std::invalid_argument);
  EXPECT_THROW(b = parse_bigint_binary("121"), std::invalid_argument);
}

TEST(BigintTest, ParseBigintOctal) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_octal("0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::oct;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_octal(os.str()));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_octal(os.str()));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_octal("1777777777777777777777"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("0001777777777777777777777"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("-1777777777777777777777"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("-0001777777777777777777777"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_octal("2000000000000000000000"));
  EXPECT_EQ(b->to_string(), "10000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_octal("3777777777777777777777777777777777777777777"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_octal("4000000000000000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b,
      parse_bigint_octal(
          "7777777777777777777777777777777777777777777777777777777777777777"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b,
      parse_bigint_octal(
          "10000000000000000000000000000000000000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 4);
}

TEST(BigintTest, ParseBigintHex) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_hex("0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::hex << std::nouppercase;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_hex(os.str()));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_hex(os.str()));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  os << std::hex << std::uppercase;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_hex(os.str()));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_hex(os.str()));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_hex("FFFFFFFFFFFFFFFF"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("000ffffffffffffffff"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("-FFFFFFFFFFFFFFFF"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("-000ffffffffffffffff"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_hex("10000000000000000"));
  EXPECT_EQ(b->to_string(), "10000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_hex("FFFFFFFFFFFFFFFFffffffffffffffff"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 2);

  b = tc.root.replace_root(
      b, parse_bigint_hex("100000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b, parse_bigint_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 3);

  b = tc.root.replace_root(
      b, parse_bigint_hex("1000000000000000000000000000000000000000000000000"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 4);
}

TEST(BigintTest, ParseBigintDecimal) {
  TestContext tc;

  auto b = tc.root.add_root(parse_bigint_decimal("0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("-0"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("-0000000"));
  EXPECT_EQ(*b, 0);
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  std::ostringstream os;
  os << std::dec;
  for (std::int64_t n = 1; n < 1024; ++n) {
    os.str("");
    os << n;

    b = tc.root.replace_root(b, parse_bigint_decimal(os.str()));
    EXPECT_EQ(*b, n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

    os.str("");
    os << "-" << n;

    b = tc.root.replace_root(b, parse_bigint_decimal(os.str()));
    EXPECT_EQ(*b, -n) << "String was " << os.str();
    EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);
  }

  b = tc.root.replace_root(b, parse_bigint_decimal("18446744073709551615"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("00018446744073709551615"));
  EXPECT_EQ(*b, bigint(std::numeric_limits<std::uint64_t>::max(), true));
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("-18446744073709551615"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("-00018446744073709551615"));
  EXPECT_EQ(b->to_string(), "-FFFFFFFFFFFFFFFF");
  EXPECT_EQ(BigintTestAccessor::capacity(*b), 0);

  b = tc.root.replace_root(b, parse_bigint_decimal("18446744073709551616"));
  EXPECT_EQ(b->to_string(), "10000000000000000");

  b = tc.root.replace_root(
      b, parse_bigint_decimal("340282366920938463463374607431768211455"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");

  b = tc.root.replace_root(
      b, parse_bigint_decimal("340282366920938463463374607431768211456"));
  EXPECT_EQ(b->to_string(), "100000000000000000000000000000000");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(
             "6277101735386680763835789423207666416102355444464034512895"));
  EXPECT_EQ(b->to_string(), "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");

  b = tc.root.replace_root(
      b, parse_bigint_decimal(
             "6277101735386680763835789423207666416102355444464034512896"));
  EXPECT_EQ(b->to_string(),
            "1000000000000000000000000000000000000000000000000");

  std::string large_number_decimal =
      "324858881193991190803923933498890656723162722618264614151601671350740265"
      "419372679273210450704528017384923542440447851735324152492856992875998963"
      "955239259238450750767153649280357198625666840354840314433695397383311869"
      "750597070202873038430977263726779047256670366652834871146529917632448558"
      "972516208572199865285922628543247289849551265509907332967546519587707235"
      "814505204521660225546727552338536935766482088729907163010093909393428539"
      "816183383829843649962302538148835093606083861099337834916881255393784379"
      "307733552579368851810157196596158529310283448397259150709216416294693098"
      "392019515911942711519103478151941980237905427155257230615221575870110041"
      "981181517195044751463433977196353426038227242173974705499842183737135780"
      "207656626242328177394499383785062342957533039829557818240727188854319557"
      "532951196908373411851437111618591442454507316142259210735070302526052649"
      "883108888266169052738822382218711612397214364371813922068770020912510237"
      "774592752356221581490585290587476445569064959678505146376270865864358375"
      "949924524191879431367628427759803639572932989566807869532333524813198190"
      "701551807703340302222152643735404275427032526079288469373044272894425861"
      "957657016929233822664387031907529609010134974351110385289627280447741566"
      "160837212471015991213921434398786867711804298238015449695529190150354245"
      "772546014168774963512796825181198580302671771627350702863800383799718980"
      "627945577319272525070209045896785013223079145608841197377021054825138926"
      "260874226202236431431372552124227336933548859837068538954898228863705810"
      "296612590267702553110623079437603968703811183838635786650973002480837388"
      "900409944973097115256250228799768370118533334080189071567157407343397071"
      "755760014024859092153143384973667377517293122628274784317132065803760887"
      "407896458587933909041876263890999676533603384368986295854162808732926937"
      "524814876930995723329467089668478420500154505779495965011714293728365780"
      "315171749194571175045264364426164008880293322521198379305648588157448630"
      "063534168350951281996379203797022681025063952651472292707663370267251219"
      "953645060419968005664044663363160173962684941980621686551652943497382018"
      "035312165838102048593639108307494113402712991542713673551819811975739957"
      "037115281582227574572204136073818277343106537285789767074131346516653832"
      "109500226437684875446018874620714008862876826629070815298240154473061968"
      "488718745624983707142359154278329915500605010173874227103146307082272046"
      "878658839284700954241440036066427309280837437515825991991804833334844194"
      "022789802179185042940975710836147111100761091282975375039600901556857347"
      "064719722976945547263084086953448557966485603323240452435754385316478595"
      "690727512215909644764428662479132680353840420791131346796479658639783713"
      "842481710447990373006816868170422175733430728120454315817672432889848197"
      "058346728948416144569711111598855317461998541123961584052395450412095716"
      "355043767625242311101295165689113283672856979495506750997615585357644554"
      "253509028700656163860313260275314595510332337709669306133790057155193463"
      "670511159426484275550487959202396633155149061544735718225419991746249524"
      "430545509276805986071015326496834935367349398432490007835889262724820703"
      "575314886949908046211246412394568810955997771962573887044487650712750937"
      "420482108151951854961877564877696379350194321495005990725447394640814435"
      "530079080803879333744377532669350743507224900764291419923144419144671911"
      "247155133457316063667637172946698720528403934573744404762145655958684922"
      "607026830282115352815948545304974596263963160750976287477879158117738543"
      "799980922993118816454953295497845068544363486914317198841625730606288300"
      "876704904469693869375822261221392503030347391275272183171067927069710404"
      "745131358929563454026646070329957575473817616347545593041495641933097822"
      "293999791994088956765803127383351166760528429967056476195169585026133380"
      "967424889123659184180052679875841686564618974838798938772807140135883027"
      "451756784060254630310401426075405113015589950292193213974353180640285874"
      "729080930282140294860048161949025618406414753566805022641803802663359841"
      "708278551241159744655226329373449907576253737358792634119937845141572372"
      "026887147401895689478116665112623682375253247558768827202667155558204115"
      "598001380489709961045990710272589635580209177239780401886068067163410319"
      "821721989123153780464613226879761326876418023751709133608847471928834029"
      "052611081853153745411991998833395532901987114560668293576521697976756467"
      "529507218109727286685960935894190561042592314770154471925660707621677056"
      "652372440702266260143243550911464325081862020892124616482477505102207266"
      "845508189137739218110873408724871457912843538457759044145160643757455082"
      "797721314106233603657857494847760967785632593205565774637189123093179819"
      "821283835884391189706092707739867342741294083209866601104606087586540028"
      "716319698499469526192283273281518881700042808549222699309573654888041461"
      "763501721488791551543444957638160338813358161400674306761363996787237896"
      "161772490606854519755251042549814692058405894767795631715282608274427783"
      "513710663809506841223829573348347252670927086336706794074285415678635065"
      "995087038362502318372065165043477168137192637720267543392523899959161352"
      "634745345152817108471396608824239186353101864915835461400634127569060139"
      "955235330117838449512675869054739177353338112779030055460422165726797404"
      "154295822645677692667854914423677456741394285098716758626400305464838429"
      "021868093466033685690595539884202850646466841146917668465960539164667579"
      "973034542592654872593093105543273157186124599292835138505579905123408241"
      "668651425433943576414643633988558809326162381730826657831228421109704684"
      "663586780182077537814383257310360257787783542249979458890463217489193177"
      "567427595654798629827326368111526804436310271453791240084467084777151817"
      "148304206535856593417792001713304578048540719816923583945115538777019934"
      "417993604552514116259781583437089343926405506047002962590607863144266498"
      "118449070496974419506175441865828538374473097258346696387861922258461846"
      "628701636244446250329007490724792013170795547992085673569612404802188476"
      "778328186696456209794760840800927484673294159254402088618869457782872614"
      "368042079368870074866423270022060638452809015263523998827251015292847024"
      "835132981549882073167706453774591026798151441034087805979817471453957042"
      "145288517050098321579598373501656090398426945829090320271120547130135136"
      "070949169729724286106986233919159356621924488093419841168474105662846121"
      "807269993909581952893443337935430328017641577221117240652207550364684349"
      "030844898473137530989512461209969655077047070477275171971938881667502298"
      "059235232184833599075689123581625273669727617631279963289696022448426900"
      "658542155129910685658635828179359444025911085900742489748876660131305930"
      "117929779446569623632413441969674906578580836937754193808928466335139028"
      "314356970960989162283686773467796117444885401949275764761404686749599592"
      "122556192698514639324053763833378852052721537924364103341693015443294534"
      "832333086322794784567042329565259765800357298677366547527800523010837619"
      "658882528228081907817796952628187675886740695944205210982933626120881646"
      "381943727735884662441838401764612882331277890567708411507618140581561103"
      "540787074948168753275770258617725749021601931011326642111529598495110498"
      "618812671873021330029307776751620674560990350254590873212514091803643643"
      "882368570378294214395469783803992942717611202855583421973073622580650880"
      "786271821198352569286411018723454837714995564867089746147379034983299744"
      "010937727373706858265545189884133103065463064999734358646160523462900714"
      "110261627808422214802359940039621774976173710949003740258475893865510679"
      "411203919255799687790096309324543161879785817224423358127633053530820937"
      "331605478190170576772618924455434465412199724375509638807864787830470798"
      "080457630949571409754044395953276463424427473253382881156116991284211096"
      "112379874440385383208622669211646453338354163537080281042989720305414708"
      "421596891365260164045972816062319467514255458410841877494783114270426605"
      "500406458380769302198600235533042876830251964129988859894499189020742871"
      "938467517123354294333838705292642459375045719501640269253832398769519409"
      "037748893827480656677076460206818395407448862953757185970663325384874005"
      "926922357329651464136311261047943088259156800926666566398864943201995703"
      "843188701263907456777769707972411884538454597784306582641990657704344035"
      "515042954531603092913432501072799960208849209999186412027614003203737535"
      "546296438875492655706246569173124142000586914054484219397649755318901963"
      "478248916540626229932464414395996038207113477512406161994803563765858823"
      "449481490440733193786410031982253070643181729731735905125812914715267895"
      "639521271572217470785231760561925015820447828221263611361671264833517657"
      "992494353867302897052649005354202556252192368363968319884781012443402413"
      "921199995395690713857512013116681178358853229167654917804497639710810034"
      "431277650481816051334406741852795926155098539555540915036897592121622286"
      "224065757504211714807736479885166057355963713555185864281342174673779917"
      "539354069578609629882087289240540801616138816324260880816803941272035917"
      "271014057062889445431555083634645629055777349613946653567822368023851737"
      "462179137409686734846842515014970873671319964307598003044507416596719208"
      "680795502171045307279279118547750085095226042077087295851815605826225281"
      "407158769611483489875884731168503252210243901747518111687418870336201451"
      "781687871355744940188139960565333193855915249931742236560996546694473088"
      "205309198445878363546192909315493403841008471348772793087720097689712391"
      "090136131387832534644460389102674352537375041332308359654337985473138422"
      "319984578701439317256516425251210716855808272962856973414027691413612869"
      "788838105198959608013412224118988940894955743156745730786702844328580266"
      "667267058028601834581010038878133362175194613232217680418170896087994094"
      "556354164077234110917679634842692088804050318420242818098811315808511445"
      "325437610495270898133077484406187838297407988342938345547185173884011739"
      "028865577955944676711088671763375798054015936835118210280902792865036952"
      "186817850347662758924906031280060166092358226398119897824377104707997270"
      "815070240932933913541289058081408175916069853120064464621780539347485304"
      "423255237995476711483190083013775344178352560063547519426941270745466515"
      "106873030509692613930174294385510372222706705859557745456261127326994077"
      "987615851613886873039868485773045159133912182743732390285833471445623272"
      "145714403578397628855389348753247463865883820740957419525098548307603471"
      "492025103570185159101191227546727993478327726433973154736278423854944663"
      "595314658583493559930830439411255599063714909034755037045851033560440216"
      "254310209898911366269117997395133585283075554316459048364419921693191413"
      "767400397744805819587073477275926887567043105412247610237899260163864901"
      "879923829872181403418152514958009658749869733152445281357311880447518423"
      "762366573999801491047502323146634531722496903937413869821705623972157827"
      "517881576579204092123394616451625234914721407043861436211486611969171145"
      "530221805266234233215140049734555351358039284060967497214670075020463972"
      "585812527920927852616595260142794969877294755910971681500671757496992302"
      "995204102871414575443173630818015470280287311279390068132319969952115462"
      "096036470856777403380897556554749308972789755641427073574562185930555300"
      "104563235414904419148977839445859826334773115011067811115340343130393189"
      "503543409259575044732268540132811679845996034275616821051705668313625957"
      "347709672560829807919722266571994197550761983065277360973086978387508863"
      "871830285267426791323244373255803173197230020836917041180549449944467189"
      "994149811289229546942824454123960445581693605148231165245648899814820800"
      "979929516360743760895830275249686001766102357284353565295428436009956527"
      "347861515661847657748629835990757398107141439411576090621180632795202742"
      "562931210472451555228229540368588048567798565840877573555715162048760281"
      "577027261825371020769178846514588534780217494956347434971216953931136271"
      "868415873915309089453692508348188216957465813791094180024218966622428476"
      "736715052897868301323792466922091910036595004680124196438146684629731018"
      "437502309982735387139165931539367556228607377990275058482165286563151046"
      "276390769611514822364607203904890778361072124357845454157488746306773682"
      "419854170852207903849495386055125722434369045425851950211819010240615826"
      "061448205134238719950975073657849338604434949285866484401703389285095482"
      "895091530725642000244494857378277523803846427400393754629706080012505758"
      "413265851186174590137908243841907664801001255233984512175679829099183684"
      "509527935991011264434010521990777546259053299726572612215983035097205217"
      "836848787528426961187104459815327448820804774928666427232927375151013123"
      "688463194596570080517147345861739363981585158725653494224213497948668306"
      "292772790324529531929109955350176849474757759949969297366571300199328681"
      "847941055391144590957778925276747313317049822307370994991004993752033933"
      "583745202901633908355028365100639876820558884255877140892035053221734287"
      "773638736721251643655442419178687751168238251337624275494280822982771254"
      "066573907953898904674755057770479458811127994649407065040971720114185080"
      "011531318560069240016993499955007561876293438830695654983023559858607664"
      "807288492266909945241096882336760880257125622526896108930913504658396239"
      "830875731871807225963274433524263219035891918515233740253994190819890041"
      "302279941852853703313248145848669331738208912213741127032725446406117503"
      "361819840212008420108504550225103421806121049212942781545715929641872598"
      "000398290630502441949693338034055319866392861922840642279647214140575173"
      "086610161849416535617251603332037398354123903150094863598635960995631554"
      "400265925779140046707385438056838871374440998356345050745748276630285787"
      "605002530061730512071507083453709855353565436086971406929220895210736767"
      "015065849188325132890083685757819826771834521005787169135814132133147707"
      "727923434072300376162524793969922157623714319829695955618090068434719997"
      "126817847769743074172217395807177908990702959633537068466451916252467992"
      "305330811003914797804327291580326414453349112597978678934636027895366499"
      "826720045280460294403226613264138045878385800158814136488353193016371201"
      "782771491562057494822564158203998263233174955229465951569072219084678269"
      "284690572819513102885533053822635332197710366283665116976118700270345354"
      "098320222577596271603424743431843128340379385814935982635680654149017517"
      "121154691420428406723914647016309572283132159571067642898031482376377134"
      "446594384254081556009155813013058176884942696073443087742711176911689204"
      "539333566951282520539308357279606969334485596815562660872031184698370797"
      "193839468983134504178819475187383866254574994988611262704826324143161391"
      "475309463279058061900987579936104628140467252916460658756494714593806845"
      "192958904038694907838831170627155945749043679878124652570085562848768247"
      "999847346099748170441350494162084583571922513604884731392450311436477164"
      "253731129028534211424237978793797034499185040951140696092497130521744221"
      "921968094187317392330532872830608161130191171548364124214811710149182722"
      "217269429139097602223503515938965168004050363907951260446010697765989574"
      "409620912390251435233087642003540741920199167722080273656242366337877137"
      "516117189078211435304892033838429600726197255483252532352772182428325134"
      "216839646269086939662913292705835283426616741865729842682225267006831943"
      "374011520287422164032382091802246304763029514312249706887863666999764690"
      "856192031164134293128448360392906752895787778308911279418285111278038175"
      "113864706580674729296238634529899956178391715320062031903937308256864331"
      "086599022909799446245269690874934193154087272501687684626795935366549173"
      "063966057642581818245952509860070600167844069093201383581334436996377986"
      "194144585318701064056954703794591794503922735910592919899834636065281178"
      "805049424850057664057364117273202611362522150808621091219841101492983534"
      "969542148154716020968509025645530633431823302425832359387165782969059049"
      "212522489091828516354648961689668467543143575515071189173602537158067265"
      "318505152508424591771915393949531182655606390838522105275875610982152717"
      "023909786510815573296479001982594208206937119547256769220087572071062930"
      "276469063684451296825007354298510760420100631133396831612893993377068466"
      "047061041739833523332756254502043135177486994708929400085378608431177839"
      "751277012817690197918313537679445283010892985167304834438384244924203507"
      "781868860266472351040570993971436722587862936573247751526159031433875469"
      "009551319672358386260001729678394217710571584218762640703788851829951561"
      "112237706851793136070185144083434614444232267344273689960125150524438718"
      "907230560077614695221120436684217657252757381447217046250777056755497873"
      "146063238176038288754187634826021333228417991361516679965080261576154523"
      "516411252095734578642024884816699301910825348945432640883811859199703809"
      "087665132208066883139897363661123928392456847955477594930864810069205503"
      "188849751340078036987209202404220254991389445246097076644525390069938245"
      "544747266377474256422849481708594986677395727307854571780593915788975339"
      "491396496885215937914753189168991139047466918629492810148135001836027881"
      "777194502842208635618144463588605722439310691252033822581073926802025192"
      "498355541595500762538151637847219195164244391346480213248840332655089127"
      "791145268868200938879462559409556645922262386002120082767199152375283977"
      "168943244888080526084562984761337131107858468400489652268966105787354619"
      "553867226884191062895764420137917891883216609312110190868013611138016677"
      "020627685938266488214810153281346294778461046070364314556443722466437473"
      "589237320858940046304678567499291006124425175530652163337164844525850446"
      "028813852649086016595134354860160038811258411543733358898409521251741623"
      "592324018833386319700921696342455050198853735956901231848775221179531717"
      "002615273347512102513736003530256720878390238041573600752349439412740050"
      "016350568368566409771419200265374051118016339076709365616420646896315464"
      "594961476430919038119654717630040009170190422797572939612582785408736736"
      "708339759407555880602777338549896688201653760380142728724456178885865750"
      "312545556207433059236307370144058324488601748605148321353807960910564090"
      "306325398326226890942889154231349515151316046437746442312382906115758778"
      "195844425272622607571808853021244800914873950411455741085807223010697995"
      "922577399839497711111972578978912486045789668108762543924657996065555520"
      "802756371964813088018677645260138424771104721310985229179540683398863985"
      "911910842915224412079199373648814420484403249952361204508785863210119457"
      "994277950890055688818947430219082996950111523176729459774778941877051880"
      "391268942942861363720360611893044112304056848838523543168785227901898327"
      "130463373967250301184638005768794774025386164554571750239533627237936053"
      "224304254928077128214086333783552213983095989732630467793966674556980078"
      "244669066213928964308773247493817244566576814076823173144204146281304584"
      "503614645184137655642509678311755336971873735509742517776816439714223413"
      "340577443305716600394022645988700893134339724231026354123890995953655742"
      "235994734028264206834705289495921017574300289101060967430774884886198435"
      "114809837167602011722411606630568883135569909103863291649670124566676187"
      "496395706522650170522959572951098936126841524803135276769523800805356730"
      "154243810766927618321836048195185292061628904553195149649201661115426182"
      "650314573358685366300497986063696408915123047776516631805616911619873694"
      "213614072046469515710228171133798709951129131292351492105559667173283327"
      "439430611817353118577319518174488582905149876910362135957741247749618924"
      "648409732021830670304711243628559304726787825785362795636200688184694092"
      "667948046586469484770825321345096966519714365376026366437182883984524276"
      "054298105718639370514576729738326500665148059972319811111638587425037047"
      "053654917032193669427835635503305913922801682897827933748706401715574180"
      "106410895476925201652668094205849597532377110631032545648944686483198790"
      "259907716718269936202299093787776003418222705809592016499706662617318812"
      "207771654846896200337983743201202529324911228277634479055260177862143776"
      "517040990650590962457348971631816060150861377771461738591730846324590908"
      "948698591195536283793204372071945466203900020462538710759990308377622594"
      "768477253334873353835635409366894839722931098315175885297956982612785105"
      "967695417306284597130342150513240695299433139963369907825569696524991083"
      "939958560696702577047609037727717708388010000814825366093820749916169593"
      "402809414413034722110218102413547426539139722431737706081164378094376648"
      "051965415172571219810173478204659510263640336286960598633345493921167822"
      "096013607008982429771311609595655487246057829853808281899286174035860079"
      "847639193322681481063970887236562563939005127260559521863116416396510039"
      "540283070934749242773700303048398079854078379096689562831406722983324915"
      "389324702195120327384278324167728446210293173671963252911847976184039240"
      "196069444014397404819356311746720885609662594526789637618310552982035440"
      "171654626322460923664552667326889093918759385698500964347351558916811067"
      "287609570206844678373284814986875625021810979071823747109585595457899287"
      "992799700301087489019584155153066993104605295476846338096720371208591104"
      "353240476252570643580895856403254118031207177363906670609375352841112866"
      "822634006043753904304147051525397675972251811301057120762631881154061618"
      "156162000065247468961850300530368901881416903397083405696148036162095523"
      "519167687329858460190718143955819122414025254662507962558523751037333764"
      "432903044658468453043197670532308813554732255223441985594018739121607522"
      "481175351588977945323125800339207625444063749298395756105228563671907752"
      "980260266966275050204773738880456926034547091830929287499318855780587894"
      "1909142123028513214693376";
  std::string large_number_hex =
      "100000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000";
  b = tc.root.replace_root(b, parse_bigint_decimal(large_number_decimal));
  EXPECT_EQ(b->to_string(), large_number_hex);
}

}  // namespace emil::testing
