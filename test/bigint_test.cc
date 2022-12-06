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
      "523635077767877009281139844278924865703716519297454435932030212994549600"
      "168824472151758522468066723211320456504318675574724280316342590670541758"
      "818271826016783781688871439202710354161967598080183593606827466955810679"
      "126680019928495945071220079960617188856354610731325967884634610906819042"
      "850845961801057493769347188100899697379582929590265122171684559455117622"
      "431130703671011120556444566563008771382102770835651640158132616108404453"
      "075629265503464561162955665188210804770137154700911214415007560196671026"
      "985224984555745489354711437797914909945278224965879858220937013194890236"
      "760135622347873549858434401378507951803564469909785448260903707685822387"
      "068121115624059259806046805402125423386186552715372867938737684439676637"
      "774097770560738420309703308772416829258135884447036931556363933289689710"
      "331801421577865587481931198494571916955054088572284199450070089979046945"
      "047412874790642995714618135244289506524146972968328890419869843629676521"
      "286272798269997210745380183318712571581048751410278753814099561434250897"
      "497761752958609852825782037029620323985136293886275371733580660642337762"
      "240408137684485095984757742955948778607601116877123693922408064446791052"
      "391183546248328257447804159956145738132685492011739046180602991191855277"
      "601942854668240110281607125202404395860056167239995061823607013953591927"
      "921229236045073074815415172555421462672488313571537679998670672661004733"
      "887748692117947364571188174130155454935532306738731482994216395224300451"
      "502056673161764183683138692802706886212624746584214050386073030828319540"
      "062512747131284018020268740333850758099114589855360051186668545593425329"
      "583648568225415038788766974636103759586150119863993961668391203765779237"
      "638245624614756285199847468922681682189142170199674520794026443365877883"
      "369142896794470119251976508988544779520979660009375131113759398908446552"
      "801172810344953948705758899405742689923980169328441024958881919509595467"
      "593889264231036562613477502524114154201253428740371382782978224849699326"
      "999006550081966705452549969201480170718742788019917709288151921739446414"
      "567031687400942217843093914757879540513773233201557877513245849034421363"
      "340077192365557315901200339516755640020550458925135714430383509140142919"
      "388325582108542199526646532649456285630469112667752274707215226744576113"
      "080823268955528680050942596328539398148616305229868150406697162719879370"
      "498304555294976225601330226438102955356744592344616490714669935452938783"
      "465178072677814404037979161448418901017192108135891161627871977728464123"
      "281519522611542685306447781978291149447080039534829231332492190150740967"
      "512243709795162738040676423409669372866406132885761691465542749049353029"
      "977715589334463494178527231411562923699842855176175121964705126390159624"
      "955712791856119378981260012252979071724997201012163472329761536090154311"
      "737464900614633731838741654436528199942360497301848309319884364821679555"
      "487265077412020714361960701885203590174991448697981032699359325794128693"
      "568734443983929961356364512033130523098451632247252254159053628366932517"
      "498567959806951150743387118919921418047443651721630170651435615165364522"
      "057031164271803971884804037542762368016749483526398203283133641247494923"
      "419452833262547514614518095956889047008655339651373745411374642294436836"
      "290326773990128437505819358598243576886447479140084140374389793499300877"
      "161068466627623500428535905742000968658704117952320101448594759057026479"
      "374056725532309440160576616256233350414978512145249034468666650762782570"
      "749855555710322961967096201839305989076696599588764348488456693074894368"
      "169196221200026468741190876220202329526824820092326469929241216049109325"
      "229430945338487867869477503199357032932405497020638575253413155793362187"
      "328524473133465952618933801090348737106944515646523779952104164041851008"
      "134737444180513142105396772870497403491922714104667743080135562863088343"
      "232259419603853823797972896160568296051412069002962026911952713394279312"
      "835859802720572469530076284763170849300340654254114139976035915154829648"
      "426680405813025622530037121868199535859820419063310478456994764774616618"
      "446687139397104085445971764930563536965239314754973487224154723390666499"
      "509657063494488140722904564477890736733707449624827634478575360168662956"
      "536071968876924831889292060473134364681366105897747785082957839362671509"
      "777268248952079682495270149274329168719178913829359998950140564740118204"
      "683212193377256768565103056219132965049901720703112717235526333452383151"
      "816832033200997620624043471132301758871540045675891109211335223254062345"
      "892356433879123939053532178206909346746348493320854089838899192267850593"
      "016036571031908148761788909590230898085236422842032747097423376155119295"
      "061778760953442313668650156253983202076406016621044241536986884668746684"
      "697189873811893720210535735763303757692154783317140106735090471971894126"
      "686874139766310316476358244499158339140575673007611212139236921357413555"
      "860033052383539591040499571710881788858563612841983437871345109331058900"
      "698076692171429236013653111659268582587411917678384077605864725416365270"
      "794382231909904561935810106143767086728992894954972615779231611948551248"
      "913294441006402311387319399859555206889176340224450925120197411187439533"
      "760896951918640267216994348277454029467904343490958326930779270113690160"
      "671179223073836038253700874948044701269798340110733101727209780021327866"
      "018221042395495298514315063213687849232786170642546762292827804522133532"
      "892620335780699268675902114558599720851719227647530703383718743634249589"
      "754709293908161452312474155453904132499480123167922368890688982026394430"
      "949871228681980507071118460064465200759503828802206521125594243289007508"
      "233255505071152344021087762876434787185805903977664006903373174700917191"
      "478827098208802879253955062579868885852534991901302971820189466118343252"
      "690999106428237866728114463372655184468962540829174280041867011751073893"
      "387405293313404996157003366069327914801429572027517933968573562244129902"
      "769441940117088501732067859335275347030356332306113354285923733091423904"
      "028501839896432773677853407708930400182070188771601483464182435064940953"
      "706590078690346687577391700408595424327998259973508931546949005160772310"
      "624082029690892723029439151596219560558855474879268802502646844397041769"
      "252905013450412702053030838712761261006020047595319084136178028017091527"
      "819486423864508874407572529999374640611656581855662755095576922335716607"
      "792048368622688075165827560355617213433738597044497478126699907664861251"
      "501361157287334164680845488814245093165868805490107042728798253988879889"
      "375978887562604357637506131402496657236464757590150187536017955852716265"
      "310355436209366472864797948952363874284603567039301466284047688938563237"
      "290326026763793907858111612419071800604858478609978918633973146755316330"
      "860186793291753100826818762659577252154406834180282075954606634775922911"
      "047367095109601679139550222167746950580238705332018709034201488839871060"
      "036690347934664352889832515875060823131665241040488967824934415104120439"
      "371954293172518674058470329108445623055646141476874797207216640341911141"
      "855254273004320664711920125028070769842909378361850300681805613479676837"
      "906853124874511673143464643281888868586660833475361559720743856295193427"
      "557715121916384414828239944354908679001980389494645998780687117259295337"
      "447238356014050692763969757590203448618244306704715314914721758411045757"
      "555742179324966810748832624827233230372101760988365396140979745281826247"
      "959764008474324298376125811880242930864538617984973666684210949064573247"
      "455079438022544435950806138763790937270549910824227565442902410143736481"
      "190552335447394858166470854726356140296153695915442937297871279046180917"
      "791175315286568849833366488959304435934768579493805530792070036255238723"
      "803205954579748401081885210434974449326568025905479828449047447522292956"
      "615516374577085281366394023714894790086416762355412103677527000325742774"
      "501627282486542410601841004747152201334053473653899921714518615913970081"
      "016876581121268351829960649046406726179633186297819293370300447482321005"
      "534525577265121476448220486628067418121844840702682099170119178690805193"
      "369345298044474360376894513133101852560279361903948198242041244896845354"
      "740815482923032443731820863491374477294787322108114668629930879532469720"
      "843823931403302777242286808936032989984719467452139942993580647467546029"
      "740771894477803638253792454781320569755398144187641269273679055927587779"
      "398505726852929495006108859734754447369360601273463158968671848418383956"
      "383685709999820876053330603229549209741794541570176734741614686113412527"
      "774361225243033241270061171321119267656066619296774700868258453605340329"
      "243248959819906840900766431232966756188148193598426843879665392350617721"
      "564757542220696295800566454356032246887482865893718874928088089453672161"
      "385002203074017713487360101174753031886887629943786498389357863574473488"
      "839879464091086997281069443976935927422632779670649410237790907824092987"
      "109806436934984561328756565173977653615937439607225765323080916221128694"
      "480934187121839608624886633678152807738377004411356109688100871552342435"
      "565880871865196209090032165039330770055437696393704694111403865194314059"
      "447400267616876775178760741880789690411680538584233614736533500985925160"
      "592771156183672365678058372126663083438089234451212816867051423542313607"
      "343715053247402550418851723629954775887485843399222116097012123290744630"
      "724923946894613955835753618709418995296104226969905882529931131342888220"
      "269992950469502351479506974690642573728248442889216284836343369193916091"
      "206539495604769407461730116057019296687750484636958197713920417593055440"
      "181664501211033867031642409771701017558047597183491966372329512956699888"
      "023233487322838408231127129204605955884820947537751082705458134870651261"
      "004982290092455407980798489393193938470075419488856522525176410972428281"
      "900681689853322172916940288592101653237697405512481278832809722918698003"
      "920257323680049823830006924240952088540212709541391379122501479934349284"
      "746280274914313000175994841323729311171886132279013045779604799790339297"
      "544674108288957213341076736958137777909064651324901927360357304993740783"
      "670765630935625339744141565510580445423624440052909724252738395035165678"
      "427247761919232324982539948523001487183472557120435988489166780070842306"
      "907029208701505582042015239136492375098317747116315908901119817932498275"
      "965587510524982528450758425311484997384074462717221442644571174548663697"
      "465469923888404773747775209144889884399160208868521452894274292438316523"
      "729004833864243071603406447489223988427674333944189449704037663302409929"
      "626558489525273051868429183755170407813611167671756317290527381010576596"
      "229703620818074055347832770882450254276285746877345074013850018998845387"
      "177705942995681822040440389562949206724500623136184400411731635446438668"
      "836394980620137631091971052861655556518418739828868120424799438956190670"
      "215028843848100203933811759108286454429926312347294861051223200671605359"
      "519782571837513983047854603364028400399367981841491696783354279390422179"
      "650800326438781072978892108808187823741110462276831864173134531795679858"
      "863146889950712983684558297534199618643439519697623419768382437772861880"
      "040488956219400359613592146471205736881333751610605341827028722527302765"
      "749589902352702958432338035911514395301647828663817115623638677498378230"
      "216436868222313961413671574850851575385242976320735100891066471362381531"
      "166707027623337982258034122502816439256560319043062983519275732910028553"
      "711218011426860637113074763219127013150758463148376651224852264130735754"
      "523575955646780890083535035356012117660133703626466342337552752912766302"
      "751179794375898359337776301775744578739788289759425100367877492020326250"
      "839486672421885651981037238271042248309956474348414654176701160479019105"
      "558803410785075707035408852199481696077143215447123536312226736187161114"
      "460722203003793121613369971021580825417976764954019747076972102324530492"
      "928376155806685143707478451552249697514967932878564586673808585886313042"
      "391929998888088828966456531717571144523904460656776714243843284130793283"
      "298484403604982844684940977679415249698874693587038419827984751189400707"
      "278575962058786012485017008285562892864281696137332211039696269761464024"
      "282911807043920029301556828715098666198962528455778412692381083592291791"
      "965886558463267338909112814695143684917858330766202750998341807779068669"
      "811037925165424848740777456044469593151169245486819620455220405514676597"
      "988481452819321039282899323661451637041962505701188071357344803265479169"
      "651990613776154457450796946447549038705069082124751299401768293874032808"
      "712809003803927277688742067846283393767550333652461442516809664187554948"
      "920411653615575003804795395370579622303056563922912995548992954516869614"
      "480325285604824927808420641067732286840695842737214945855137738901097834"
      "271303575166291055558078932106241590848148369226522822226816487288794941"
      "596850215364017375584933114179664448237082189560285857851124665163842490"
      "575962890992649493596111044524794619702826846698341148990352962554424639"
      "507954006857571278453591702953068573862477422820676189701855532516060877"
      "055711999078787677501717951917669821068196210030520553698884541526349624"
      "255364725950030408347945700238430427705235656058475853718727280170128231"
      "528811430052891499434826340969042901677274310461535384280771068329126642"
      "968219242294791189252032123778373685961896502818406991578323174055114502"
      "841651276776700928642591785154433397659623896877232398881070380757388600"
      "550296113551550563123808640093913628360101620670605064081769801413036852"
      "240271682476684906308915985687960958170568962446418640689740975692145708"
      "591959636025299359680858582135145614977446655711744357497159722743521075"
      "805252123915833872223369148688892419945460382179549283706594666522696936"
      "712692674419261821838306120337357735965199808327875061205932380906298780"
      "997655592739133587646798325613466021707190066096063091794199478769710790"
      "526831704485587278221834429543440369916548732193717261954073910441633698"
      "305142325575217586866171578892430337280554577165532972539336965664369007"
      "685252128585942113061583908267380107238236286528230541905736935181064700"
      "400979303348919710022117369434850717536829051483555491796045435053826607"
      "597998092735197721876468736702351556082369506600220034095425796284464173"
      "825789591898534741584797442172006348737200779704929002004491591267339200"
      "090008029134170763274236628087835798992277368386710252175081497593682397"
      "741081749545303047093959349094811018109637973379203192872204206601577125"
      "692364186524716784658317005969946384181810824970021069790307621606107304"
      "551460899083308191925663253583966656000857399251365325746348591008976019"
      "173237340409647010823689513905339189226598760618030593290755937712360045"
      "087567523721163933370260745118526245466263436374845041064227563617771903"
      "156885859802569307599335724831381985816463019760729736245001229394760554"
      "061649380036208452782334688768160593442722262288492087983536347385198067"
      "678805534644680861437625785875091632956135420718794077587652945722552875"
      "243122968657568057026242996516398643189643510886261199255215766893305485"
      "478440471132925442287792479471084985082688884969553476379520163483555408"
      "703324244274746744884518347625290240137448052505037245310647943264534684"
      "814243087531279702189529044014473224924497738848114820884634959902275734"
      "758943325888760971235816662036062514794744766071677636272682453529964323"
      "146728856386724258073789028987173364901588627763273635188936128154695268"
      "280293739229411034818642681997872812398321445313886335281209517718877842"
      "054410844655479788646366819474518773809098034184007701231493423541855329"
      "703956553986641943439599872262885382920051013174565130422200065536427426"
      "193819072891677754748212384969303811210324863780102840116468238572179073"
      "611212742945583850498887349721181315426739595786947621271946503905209627"
      "722179934100918972590464933468752997853923960666976631400807391464508955"
      "679236786524261216666431060802550519634640306988220620627906248990035838"
      "158068846888225003890367707034834136972187182412838769121793486493248639"
      "607938805745028565467558627842369435622722816610835977500996083615445963"
      "108480874045276544410836847483480819439714297799799316349582806334227562"
      "712058948601008719976702539860722003303858929293021447620008798782997344"
      "446367853982900267822520407977494793589735142974569377483336601184214880"
      "761583172607315717368908542546661522147985714333497616404633738491234178"
      "081875287745917582052589007900276529150698104248219056086083507763645656"
      "489251200334338631377976241554302668007473184387085010022963769865491888"
      "637508410467017869166131512644448278597964136310967485545418275269549573"
      "088233990226156197699516740373461079609779636765048970323873911780276834"
      "905095448945202338963206262033247842103824820238649879018200461477248519"
      "833853982124194621323280307052285364548005665356200614677885428170256078"
      "481504379477429346035354493486924864858628693888758013728708705760436066"
      "575970060418399113046592573478581070518992944949546243745940856489009840"
      "085012679578577870173851105975085365088579059754288447705765579975555205"
      "848972810648644530968219379409951823866739034954737595233808994098442164"
      "630603177138718560753873177928918747522275193792330865941086610664636084"
      "239927493784557667664034237791061495234324838523893682915007368447217705"
      "702037725028493357216858020141012284966962000862902010891465728631983361"
      "992588874461151633957024922275131012730451253731743161724659333373072049"
      "983456716566247255713010569376835565256592068227997472179622907809424759"
      "968378620716038210740513909473888650631039152204424811023453838700715822"
      "053644551690935390546101443709573153392915362624611145970792222727524018"
      "725648896431034779019309839365096242820396096751690883296929079562894082"
      "038705958585496247466391080529579132629473207784943513157060234906754074"
      "300792787235582743174033336919313116760703834644776934688739816266648314"
      "123579819299381744536620951115542565670902980151873244014670979219831256"
      "554143613204761271214299639634121598393465910236298432261778023704216718"
      "748776798829255431460626675113804275952088611017387671031070105144690818"
      "481959336139020483343514049221488300838594936419666222092281587288830971"
      "668245563968728022589870812252986327745838538789019078716463539742632968"
      "706858520249965121950386179303595172152223463299433376389728636008575491"
      "116365726653791667172021896587286501982499699856576729214525928588691121"
      "123626664774724444891390398398722809724144643845554185193636899067066064"
      "515138867631197020208313155886445879022902872377564467161970132425011565"
      "015491162112095016264333421626763697523278337293148903578264138837067553"
      "440116353458994318975965000971175804621700855567340501512387707052283584"
      "054655631556960423561685659548331858200271209113876485384153495872221135"
      "316579712004326684485284265573466874655198651306110483657730073370543948"
      "264382774747215332322909836095444868656398297132183422038283283928289478"
      "463302745814058062759968708218191142182710802395488820438477952171665409"
      "098827245106424738811882102310495687239733722986957760519733603501575133"
      "690315293647684854175143190033726047834532858909311149391245724699241968"
      "632922971424869376064671552067292101743357785863086947889179893955647731"
      "154076195771805264689208474758399075080150512637862242836592474863164458"
      "265954754271236703853612080771867239387246276030534260450791215181895505"
      "895252312132726831577989158210218856162083649278298259829133168472799129"
      "282032693366160010911524633481984272861643435878753057665686028541353794"
      "429027764773391919265968698756022461359739325507431722437832671154748817"
      "800965041749535712443338659883154073575906071506583772687303855177282302"
      "715356600816345016968084925644926917436148216500482927828267158226335402"
      "842960617874533058834076339905174396261112107496342442797589522657447950"
      "013613385998193318551746326562842445448813704596485521807521125633948755"
      "227510290685879027971049314128778426092206451760461393173076000217286858"
      "628359489529470188977731004176573180992035918167645910466246199409260397"
      "284797023152738403102064983633497129818958278704357667841306229811661068"
      "424958619603426052350723952879098395395524197014882885922186829300662148"
      "052963134234372409327357132140488937603872353786713518673089212862343466"
      "392023466452252872634289351158876582625602009064402850226938080938724363"
      "009901378826029516294945846005677447278083470559492494738709911111757673"
      "351451654775163594222936027172712089465799857598259115368910587823043665"
      "551502823020782976455360684245929177763355595734031773929661485773199162"
      "486501248935659169064834932643386841915329749301549129860667031746230851"
      "765847531737940073359546590679028149024661802266526711471308133335927357"
      "848891416790774757990283923054080403565962000433697481763507652413605132"
      "998997986497933448450869549483133524482463922067573546418078120499928738"
      "198600924520988972798035572887062477495977884012063607349032682158698571"
      "220646325018217417275629318559693126740643887032488585064727289009943033"
      "896959812891094141174320576856636913751562236248841883058381114253776064"
      "723862598196370789938048581441616131751109952995441927760017405774642689"
      "598095782808384270501981312762322895611082210829133654440971050505087698"
      "188200907670586276794304504058730852900804904845088892034463319158772499"
      "483370021254565191830559437734367289982708830034618073722766448525264552"
      "065734720087046910509226232624013526453142354953065124212926042078856633"
      "311425244419566828994462402313299183582187085833268397111283059223509321"
      "322133959145720075145679034775106395295301537044994665268946989373072455"
      "329630505296413439645206320903716808877287534840963083713658554225411553"
      "028998494954333953799340963092731632261159668976219447466754343731809121"
      "910039641983835279865492497392961389101643540357546410032480429396288717"
      "244084116641963497192579862425568018727463495370766930881704861450420662"
      "379016369014775926151676844333500600953210763376434344600572288192768853"
      "068851204543609337909384996085872971743385143507999566419964489086637440"
      "598742445836479384625391920425871286703817851501921890055423779495494329"
      "854978757891925733380147168878435084457661167780438275423543668934727550"
      "038480695209739067137687525699497130907869763075881520223133162016176573"
      "144683740506735769275875343266901148632001218698013307823297496309825844"
      "780773753811996260438051496193617537676540861276580254221452412362580631"
      "322840023832899954067975735497582463347382932062856563852555633442734531"
      "908431349524779427242111924737240171314277813970279381531653186221423665"
      "291312281879086313242683564302545580882990179699417912636536215808149099"
      "724809675515781398292232469040774952421354258021207696778764978746477015"
      "750693356650788919834638929085551824600291270032917314415498162238229809"
      "143399330362044311016043622489047459822610240712267345051639667044044950"
      "357051543188883660264234377761628517811778005318131574292388832774797507"
      "964061777423492802608160125734269225996032073709198923635067266880477617"
      "523271327785056110281118761955629274015827281781970320117363393622805649"
      "887259832491412909657301187316990624987717503810312440213547769525511648"
      "630090131759783884982172897659535125841818763534055387744175940096992982"
      "217366463729732757023209263358895495671751134453286202785344827744524035"
      "181770383761502578448859733790024128348795888244858019684706012884318863"
      "867126741469079851169107777641528395742833345473742711050725801503676705"
      "784571829137424456636274787851960124749924834044697492354098789354908552"
      "810397986251154539403090610346185861941994751919220000984897538542019080"
      "677173580335057890561001205398097744144930197364963655441428962597258027"
      "407961963612151948642975019794622235147263595681174747595934862776011887"
      "488724820508299135464699161719782830872577622032221126804592137674037757"
      "773643844504817409407284348273033737265845394408791325398664786680112388"
      "349062875707906746391855650088473066610870211794932359734095611042301233"
      "818008337027956220500842787573600498082441490046795467810954201136522856"
      "054182424918272700781118515898524221137627386867347570015403578000720279"
      "255447937968072881139061850088240902195305475116009441663025541166391152"
      "390737291930982541896422115392340917010834477172415452988786568866149456"
      "641711254386222927247665037921476930382363894796562785125436574021154632"
      "728757759165522092481190099285659226697155987870969185016050940475877159"
      "093605731079395725105907950444568651539294909128330066830717625971727036"
      "567349862203820750996466013116497566062534241514028635723411821297953964"
      "922119815730132624295915447718365851500711774650163240484178164354940640"
      "244325806283467025945571208259703352619939246593515105858744093323088743"
      "736032848510604756436589938078700856887839959316393340995633108307499425"
      "832391413715435775047617174041118173464369830444786986056103141051046250"
      "956793824657564014182160361391886039366800393155291475872474703028807631"
      "379263020877310195661851508560545763216743550753153354541482328759405339"
      "564207219829741142261684434212226657506754780368087519518349273936954044"
      "397692189286264659920343190936828213025754219004579966609953461868837242"
      "619543733493441790258285364312338005803219576195955368387122857559048964"
      "549662514536270389497706570385130850671849923861278162598206549627254785"
      "775533010393026078305240530463566444050907264147039182407194808177876083"
      "579896418226062052727344724179070637862267494927162178674239282040962290"
      "384509837501605929054136383926737200669428620556722251792242441279406416"
      "129793817177790014751504064903565942569818170516679412029259543272633667"
      "190349423832427130234625063608479320897659380051218347451194781085911902"
      "847783902028100795398462874166656918697583240434437157855836944710037450"
      "050674915480500336835230095385838699228405091738444436296832004539562007"
      "393167774611340678657883741604763901921657609899966866828288039981114351"
      "033355775534648917632637278519094817361770233278918690237947458830543862"
      "336801489997548835668315340581407617594757705212174702615391547906190027"
      "768864912509893496950132331744322974270856740729928728855006039079237316"
      "165641988759788571045164734824621631736602193253576550576910268523713263"
      "938301956406829830227083184806492542513747680626655601057700974810916142"
      "041917330768415638006642541898494849033056494466402821149661451508352278"
      "502361422895245315889489845582386486068941567627634385169372248893221541"
      "966822288974827248974645435977664694844221165553188072840968656455477251"
      "641803256316829386821260559695320391214720717106325113111479966158005659"
      "488287656486469813613360938013737389541635635758015617258746516643869659"
      "026111931996895239515176509766696588558418648093543313389758064291962565"
      "267264217578690937905772324456704698495576106180038998487465070333593243"
      "737449194931873305994751890719471687022738909731219648345257666669812350"
      "202388137088773108669056176549196911224444755168023191967648841327182295"
      "837564195220505009623130292169227505678099405671812255689537756760496712"
      "539706996149638283782734203557505747699274579077616081786862017603599672"
      "557024233778023208842548199361577570588635642041042171535225979190819287"
      "953275154028784736342790794826821608491564465031142531757972529283592804"
      "347651282613711115800991269696487596950954072856691387038019035177777577"
      "686882548657465003754279348119848074315567566111181377080842019648837006"
      "797640629380387968081515058464972787623846435510614815418169690416256992"
      "713528447481721390662755654086845175590379383298804427981174143044527443"
      "049983137361678799522523036406917680054595034871624685367753099610352810"
      "370279596871175780588503535033011379649996979362134280725815674340891202"
      "047558658701567502159700726180697416241775298776193052442239392162014359"
      "231195766627277201010388366118049770819450066905265544684092885625281692"
      "937226640452581539583817621826997568386844830698147791078196824679260009"
      "832728550482258807262121698815638416356660955452037603536063957937156099"
      "598440775775726835744864591482063185715238474020487897194613993313555160"
      "040722533315891457978029783497539590367239717199529877843503999090304302"
      "782126405048558680341516156054259788460020519823840228192206671503264156"
      "191307608409999262158106155100253104287840845130413802287391989683012897"
      "134397593350762586570174018455463834357579748435693242252620652075317388"
      "036994985788284836780483868143620007535904289352438111284066283775781617"
      "352416871100196410065318877489161232808812238104935807648623819374320209"
      "074424737994089461849123366216677979447187003570157335601703003022292372"
      "733522887174679629252877191055069600592056033508733978188382409312743513"
      "088795905957123347771404716330698809796426414015414318344084610973176775"
      "622041076203831250379096462087308503248061031292801294039552365099300694"
      "592548031774921938343648978989797740795427655046342253494392859413237272"
      "334648469464326524127494843769692730513001421500882890003722268570362365"
      "309371646156895033059437521710967493439623977050394213001627153305135448"
      "061177425278728442130939767723515914095236413027972936187671624764391965"
      "751519039608004840044657187720044290531597502266885534177466658294802856"
      "887734338920913721256364459525282024802227484628369083526751284677836616"
      "809546581830538875578129092816789323933939747412194618254413997488341056"
      "925013330706345873623147434289051048978735273266382593983956251420748455"
      "571762392225479565562938397302371625149114547049642649541882476530496659"
      "586984936977662116659326177192054900646166796644477418668936122123684966"
      "394410900689118928410216532074534837015696282981689369958893807089850668"
      "126818452247209723232008990991016245796748810674678315376101596630226208"
      "311017107762168213159520059079106683935714398605903815913970451702709337"
      "859559887270683126191040482912340594347146047261253365787766272315673566"
      "344195437138383662230409138707005280869260641153156478625151425023799971"
      "630595129078271662412695846310595823770136348992904565710375857258149171"
      "516997895587049758524022038568396769816785023232392506838558671234301371"
      "090552593324561757096967944818941166361798955135091363164160936746936020"
      "462301057035251015119695472195518732419386514211844964303506978199657108"
      "139703995776668111583571684210282713776010575232514319863629796845351481"
      "499711129005628259002420210770509096406396270700381728199131607037178627"
      "843236992713640834683909524326244756808395421979149510376593152017616579"
      "795018736612804738862811988361899380163514737828958638712416305434508963"
      "200339612304159060068719175848425841970010168284842889723035160407469546"
      "770076852402106318112193920807704756960213879846550028937815760893465112"
      "701959523208360834779807814154946688764448059713314980047154803916581967"
      "834014035152454774397443830541951689917332132510476153674318844768479051"
      "729587327578438405996877994273065712004301519751941532927522085013716271"
      "982103708499983511342730399687454613907004650556081725790817487811277037"
      "456993767987574122808412032404421308841446738207920654545477141959926244"
      "918617660401072597044332586545465281792110601598777666183043372996409884"
      "327767059532001034716918733016612078373810893530524422821739938157648482"
      "754238387941980344722639465881202553453555821452637907369354360763538184"
      "334636401626489640405454686977440685842095851908335274983189599119903203"
      "013115307353394713484822640927724637727908359631214526498623720283659042"
      "968599097298693706154965137627161082959418476464408025887367327776947604"
      "591289774988508273289457897768908944092537235929091997022859844114383036"
      "063197986438731047377974593032883404765501779315703712784999163672849220"
      "446061328100879948387501432792066244969691070132755619137022074649227586"
      "629529971048352642750551575719315377302009662981239999266266509051559477"
      "070112542933907678740887263792038212431139814972055913049413389849723289"
      "706622706301864244531695065790964131482821486777811485729272872415304779"
      "004191493572029391638312845779812842768275446190592798583951332633735795"
      "922860579363000563026551535090751144390390071424883128514329001347093207"
      "702078096590164039434952344795560636082555037184237488472408537579345275"
      "582998307266411616114839791713625468064471815088509144338273955475611076"
      "519343591212019844820174727024360239889845495392338695879017279280605974"
      "740806146855689614654546679921931509732297262156004236336916355367903533"
      "322605833972811616964548655343269162612825072420463332950819176605003447"
      "401133586473512661710787844885460445914003328046418419470079115917548562"
      "771691993123646725680586130089416479977554367806853416725670091519189579"
      "390281509231478912486574853663469455528278202264681386057484464215448624"
      "732131879417718715299136646699047734488165118339982229508408473343045522"
      "230356278964546174765422821896205862114065233841943033872614965545373910"
      "471197154075954320737119891095850579955348766809943671921397048075546817"
      "634807491781220843541995731439946748241094897040863801326879888760451065"
      "560193091260153222487052217432002831128661477736913857568330721152694093"
      "800057858150744358780792146332629668064970589971210282985280648954061231"
      "261996043395544703301589161185873916227817283300289701612866247501262429"
      "816251511508012028308590614664342715446918798356931403238258529400177919"
      "760986074854238691364979246113551969495679410219938170921715202902769939"
      "814572633411728818863843558812084882159458254987981629602269482895254974"
      "760100412983366866533624786342739620969820243168757793061618152201663443"
      "151626040921364360407936839574426175336075309392724423727171794465683276"
      "321872173227326975562699623325788709585964449201407937687783057020947166"
      "575258983946821974701878028045831834088382335698350114903857533455833728"
      "755364083633891981935966837955073256287753700956001679468296037426636294"
      "011266713914613473214292879336671087761155607008261074302213173975772687"
      "075360004926046527935718292873091282846545833015177639229677370579265347"
      "155849489178578845072760773754833516066798017573274365916082796713813133"
      "137346463178994021605208070416834046413987567470135985351408266050297068"
      "512045358542193395559776376025688958763779894251362837407731404577677546"
      "031918658801962830300928623286559229129070296500268273608957864307793769"
      "387088788660790729062641934947040160875051088042682245948935917505334574"
      "043062237814748154770639145325075851938543674377765907079967261230001860"
      "500947415508759037130236296209545856726916469175122058505287335914334766"
      "448176902762163803936007354869059232178610175308007021172481340807127016"
      "901324858720931353514064560725180019419528161438740587150313885345327465"
      "185619980649246575800278198483470958243924606624050238496346101447462778"
      "127560449464515505268338789812521431356523875146861096490583329458831385"
      "231368131047419092040511488831256691479731518515087510747453642775829000"
      "675249312978126186922194252670232211457226125575350612879959833452825801"
      "918177592349142449123775092527399880824383384145897727852098633022329883"
      "541124613084759768398997038446077939405904906914031539370625627478656048"
      "530581273757445836479872273122442809874295843927614364227739210834588524"
      "023062198516559425241521083749764308491962084119069676762182393515421717"
      "826307835412311827777269568706406351019690803902680992099600745152760942"
      "960857624915112167897388528245745485435493966313891987209783911429298455"
      "308152354236031739943546483490717091946119224991191708701306562268060873"
      "428677881987720160980064341653568625286372743153785649388335005590392878"
      "366942529239343131891098062582791476615355034215085516136219539909729631"
      "597368603814647453970817014653864279018737829645643222621030869182268295"
      "126457598909386693942605922996114425189118606891628362257576231073688039"
      "777139482212720288334521716866932771884443096198913664093708066526009816"
      "887614130035441768516330383251274133420721940897574672565494846461942252"
      "245450476712876444616328912338705904012043554116515228308576386059526291"
      "823238814262091316955352735872261248931903005843686064644914331304363894"
      "222421331808102647492640478947709390271385584911752567779854178036991828"
      "040072554221978954848380667865473619795336327917660759065344681728422879"
      "928825412396479271852123025635185481855791536383796204903256381387484475"
      "156435849113318843780453654314662982485454604208592852215698808578809082"
      "849478530815667921037863677772527344840535368983967465507600748550441330"
      "730972643091670369610897316542901814713401939186117564284156469786626922"
      "225973274661112922246077400647370962642159699469934868843679487070751132"
      "500115286036920752955151691913870548550643599922446326189826466369678297"
      "882822840126882096320634926642016387844690066865023882142075914773496066"
      "102416600990247004667022000764101685992390730594864905499206460223536295"
      "453492295261226559435660758784624238287238555235537605980392981462078472"
      "504439632978882320055601592148826776714946028327111097298616508580925255"
      "317581501662222572096287704559199715147154774347660449965855210336470363"
      "291308778268734926557731391182020688080326347829625221297277215353682503"
      "842333959690387729413852864379053129305601032177772902091883945004303887"
      "502081432318717792992751142374257866900756002916572771224832442987168337"
      "156283406877314315808052244562182531068824770808307075456591132213312487"
      "120765392710573732587568481200848986363707863436637369872286761256219294"
      "351075254793014405518446910096415569912425861157687227262982133312549372"
      "187413656666516440599510971723492256880584081700731442817619664077793478"
      "689048069515875609459324914323666212440868138143192798091148643698145280"
      "049678200583477852310814768144107931819463923480807885590636450732303093"
      "156734417931140131008714404484528011338851876080946462615715587234758319"
      "811840877300825952389976492133996451251673010203768347614663317991364758"
      "362656300098219871100589093804743051011328991914407482384879248039872144"
      "287955691916137867571651402462686784595814635492460719463425081822618033"
      "697123528761723512105314266815715123363617850167619758373014684967238396"
      "123986878142965521004532722807113311303344217281926640719086882221672195"
      "837722423394463414040503957264147432196216754711927209854414944636488542"
      "598940922465966183875410064260789961085684054839545792152988022597779395"
      "384249014812944112673196349110891777281465775715887001917279935892139793"
      "071315413061881630124390814765439265467606248397675353428056975081542300"
      "863046896728345584921889510254752412819737763699281136409724681031433876"
      "428222302548346186129455930968084350092902352056598709383665479205880499"
      "805757916267972420011808759079521195912312271204457440619946957237295244"
      "483454751284207000449761934033087671010626418112474918611310802951411667"
      "077680833145806217861647014754895003341334532458223315379579664154310013"
      "035823166516276844414716994616115482142142472904932090404358757861776667"
      "888355136383666653570717566338849260242625217599132691876953696065581616"
      "583315507942013267161038416852110674743723649307265943263633198966204395"
      "652009495458778905905330605763001849588786879299464113349824628009176787"
      "257249971079553370587095628219685238064021866186819414931026454251200946"
      "479628123243884647823665633729483483349134750219840591410684665737241994"
      "245442470072648228251734534940480972718492061100522260440495170133031110"
      "871434158394575793758577663526329218054271633928329050699433436606703027"
      "954487776430963437531318999919176576064837344844510107535769838657657877"
      "055981454890798492475234474979475807862499667102694980938503564170044824"
      "694995032531348754241724504547283302394770467496211085007775556164784548"
      "165729478681415766375792879429420318718097149970643092350336781361782635"
      "035512110285099434205739105400221728949581738464113508751930656967051959"
      "185927743675982230306483399934986021265382050991702821928566251815348582"
      "742843184409305211444415272031778518304590227706272347147508423997572507"
      "767315954938772730985356325166872883475379699720277700466351138269444011"
      "791708586482038846140158525606458693047266019769366815755295630371774277"
      "103650210855715325476996202163756513624926070774558776399355731569712426"
      "074937692212993301782881076885900215211438023893692499669941557730767886"
      "608211446061425135687323575853393222853397799113334356611270961887786060"
      "566818574493442897540306531130048640649255209042003180691165858498774926"
      "889633903907630313939289260056164079245937337668349897340317023984641344"
      "725000415292790115689390345442569725113847334752668532590073148219325919"
      "177783749764592408057266043863444344462772793999211933267122370729088085"
      "593573794021920220783902547521355075660928215382186378938946010732148161"
      "023732887187685710807329127760274899529543350520340546204074159698697143"
      "093668216910772224054627489431491383173068841726053898472152285835500946"
      "135418464161134097971865204021459647964850894066007644965563042813620275"
      "637993611423994780236067625323245102122935402609953709581396335115938102"
      "734287192805472489169163042663191681481366276475676322594882519666775626"
      "923170801567699462650759956001448972009546109070018358995213286885507649"
      "434313903513319494149045034633861643875080207011767352111416350192554204"
      "936792186921923426614424783010885990454838814088896939308784904640850038"
      "063971031610444133597478868032643431008006607255690404171723906260765564"
      "065094369491103569744537007898841169531298875998093307640034265962094927"
      "845461261940339074962615013268891079424260529739291065809575444581417831"
      "523104102203172628547883416280866361859006336797912784661346815640770328"
      "348816612874736907860740449015616292961780822585446041555741877287255709"
      "382473433821284175799049284060670633212085266192292576319845763639487328"
      "715311122861730637764621517522488716014845797151538530782399319312080658"
      "816431979541340391521801661357770009476978097396952352249526822795744838"
      "777193345889638376209659278457797786428473136367651955717456048385205686"
      "728418925717090528551505029644471347058143830556267871339948765368484056"
      "825235049585741167132981551040507915292239933788989601493937683598130668"
      "027649584640182861466544254781708784382137566433571890014080850520028861"
      "781108255231622080272404364570233959591553555347228855414800821891385879"
      "006258464407111218447611641564637338473073467767209347129643670263442788"
      "687858637168104820844417455410521245169724195177126221453377355062438198"
      "159221296369003602356977013210081812819636677704626891945554820110843746"
      "168512203973966391401119130678932020977397706042311872749744748631644303"
      "316007270643954074590741429320337306768258470850681216014329407736915610"
      "980942134590675437489733875386634446644401950167267398861318862172966090"
      "742695107700018438167421100108048635118758837887867001646951049008448052"
      "652711383625192628294719259345796501722114610376419166413698281897538549"
      "408990796888667027654719930931648750005056284587742252803566105027892168"
      "346324303683053290222443989015212911968503953206609421606610708703686714"
      "995524565395314597816169470896388415791432002774955282077461080533771803"
      "065311924128233808846946163566702357364063766107058696954902352439059773"
      "363005940965070843470032771798000616624259102631104848211704972161793567"
      "678275946733625455221555210239492749556721495467688403373845290794335583"
      "086048867093934795048286949956797836019418862727625308858605499595399806"
      "772984253099784803455472207689877943574643812223423802366164188379364937"
      "114263528767543568946949701604642520128493552791479881494999709865024066"
      "357487119529254098747925206661458677724026885096391893022722252324764994"
      "726624014955499659436144934219754785393375090878488352054794730834922028"
      "350207229926262258117312083314931636985748939503487475314122332219077613"
      "706636182302830795424681803661357969693279584507765560763314866835712644"
      "764531749417007927160331966591689441034106852448163330268690884399784933"
      "344932973419836243760954960274007881790011462597571248024308069527335203"
      "135697741499217567721741444006352406825868504149393797205545393346538558"
      "704670404834169173113462978097432641637104652190721468843030476389120001"
      "052265676885633976868082112520565306714357192777528573903980910486296720"
      "157301984979321036822016937635214356508915659263495305239624346432204757"
      "617582823061978918527741310151726282440337520675491263350281004501018795"
      "775225726841859680156505148819089719958229400266990338066008174220714708"
      "091523602831877742111158757782374708756197060863917285277609047637800267"
      "204060925878034029360177181632639386578007246097327435582911125663823848"
      "448469222326315562838968176440694083531173717631361334569553276731466802"
      "015330853087387753677612477535922466640362514402901802732229150362251358"
      "915461039937640618122276433768353822545878322200677118823336215814136657"
      "521956934032440941812436917226690020593280845532403077913776454624438933"
      "530985263814690938958440044869130159680587533711403082386122420543042560"
      "268346141888735155782822486005866269213363042375506784574843113015939318"
      "350491567950091566664844077036709201074291342087109357786703025921164887"
      "503887464906069870715755692318142687743277590843254777940614031546097237"
      "398124400681180868617373311848971877178506731424068190549567595699592193"
      "994150717140139818866227659456274886409038256976767297630605106995610347"
      "577275242321104072316481672562515336668347118313701332514354000508033560"
      "397287270006618508776413514725843252311315457587928984924683976841174575"
      "159454159478767875200149707333683012202685666695388889179565762545447883"
      "154467299033258103119076310942352436369096755313593394185797305309863398"
      "542386469171886728598467598584453865442882758916832371633886866480009631"
      "794367512296841751623201418138604181456528922216153496377566190156902010"
      "951598699136334004493752652069937378324314976366527690078658308955080488"
      "006868967828986618411225538931974395328692702512872103475240622774817510"
      "844946726008028365358154236814331373882701044502166403402429870346837100"
      "882176962467259900712985984018086379455930813954972852844165979476674660"
      "837490035561692548572852096522424937419998405573955302577117698893046524"
      "961491043157052114356531891987480698744109420882181937729807332005577673"
      "000220470405581893313788474075917218184037028032769345054575012072673648"
      "068378428374452944609771587916476654856733366910834236288218141090855423"
      "937279682679515210751451966090939131755419917724910810842480750411759301"
      "097601432740590566820690508386280507524690359197616020506922666473202923"
      "698153687192640363215400105022633753731556224426394001804075212880861836"
      "731360588032655606336754236796781515098246809422248526748911962001488913"
      "344618750787872777066441847379086134229196695825662512569177171935201506"
      "215879777967688008070183365642804834070438086136879263440195423571281834"
      "471930142345411030071574225634725595178620149137569761799054170486963066"
      "866564388958506796672972994810336381480307000102681526038052536958026150"
      "875402077669236821054899855028719708435698197481693580049394916988373209"
      "671917001080938508586021814758676459011383299140933687860868803419980653"
      "903474736813965051380137179067846031708678058990232376278525511885771730"
      "288494249416596600671144371288759965739373622742227252458057724038383971"
      "860012823873386856209179267792489609826607495007379679782657679997802631"
      "548574482196738223355485187954513137756167029425604393804994809459621717"
      "657114980378771652556648148535311787470232637361730248825647892895413732"
      "783513584997270769630955173116468400056562954052571053852253908112853478"
      "859625977631142835252764952022297004173325499363664209180433051445066775"
      "159895327144427453243867099673855764016031816770412297550383907137413140"
      "208761274105472229418925103132619458602836000581178827055955980391671159"
      "110882693880836555048597738093592760984538538685723973707161328248052634"
      "062120735618110438845650824811008733930068725205254240850390818702077926"
      "596729320079570342038379290013005978414647315505524015195321370649602294"
      "193201437370553427288761923765848693767821438634158625522193842415206328"
      "824607473176009345111248739955480878066400612238060106530657115713746963"
      "380712435265804846066142306074545236711234308649238593347933464153148838"
      "602888056793494601662465963049324013489361096988497709697880792926419687"
      "990994531692252391704164074282034593422990501199436140477036176755277028"
      "675072126647895079885607185577864805265326854801381118393924557979689540"
      "260761650582227145740833202066309052524520153627804678393979557608409153"
      "993918264250820950968272813116920294202379530587511577115527488554710348"
      "199680907248031487588848754900568130891714764931295143928357016165664722"
      "522994864451327892455737780334156573380369159214205173497190169745125863"
      "651900390487551644789644875193723390193118019768029254159957256448579704"
      "068058624979370522874871257737083022658175570393978164055561557076346001"
      "489551913350965137322372020539238227693037264169117901217391173439113497"
      "982906566640720510124874782263457441470283385755106220847395359103935145"
      "922890885495995543842141569987868812237985195005393834091913450236217313"
      "910029706081787034645680987851989600896576403186969787419020211754361237"
      "104027716654851775123254237352231883866000454955750297985832013400774354"
      "997111437750946990910801442533348750699839933677795979198980031273179556"
      "414696088811250678587761684950162356571033078614963889560185582812737203"
      "700075008212019817446335687523276854293136602779547560707727438928936384"
      "093023769908457076270558290446772778911132912839671205434663219583275206"
      "085004078372479727876633155636532049488467382028070738301500630369523562"
      "699752726335786110532821971560490681650854817500430888498762334355086286"
      "433626874554623617472436308831147853171331233102749155333451814474487692"
      "761060141127798984671186361530936213688168119424776381165672995396897852"
      "317708960550516393912607291644087059292206395342507100498889800480975126"
      "916503289765479572927877650201809490364862476981944351214856252112111508"
      "860739029172521253141322585124998077261959250458255378376242297293819230"
      "323650999540568323079444766419681342146936050910150061429633692786654930"
      "557759064102154131080941478184382613805770092764871449127190239206072782"
      "078036712645487661695090681577797340467485863002986122823211848265242587"
      "816677174496258650206701501625942538474849573838353607486569769617164463"
      "921483321211484751123634248197306511894787819545684149596917535854993866"
      "028264503426568866391760301058225392274126982204745340130246252486693329"
      "477924483480003904462649168269646327291964026329872162746357199653651989"
      "506028515284480333642451562540945849474240814864089891322365353569843698"
      "964616978995735760297961738091896456402616863721980086807385540571246502"
      "010768891677407343859276190018361060792602838659628265949712941035934920"
      "232969423289443368600166064457330346823639229338643217052619285165841692"
      "489845763628743545333380190745274030020762157298119559286699109379102121"
      "557597489116063314371195236899714627971512495718266913727986101767709071"
      "989867589028274239605549700814033976774362652271669430643324175814499643"
      "468208859504603288578715492418901807680629572347684493876988932892044423"
      "105498666191977120911496778886128781805350988957193287130882868099397020"
      "341942066691348263594262550687127485762401882797092510800790277824915344"
      "941066187657419428758173639901087498255421283000408554180119116888049718"
      "871424556110800869975260632404706799211805866068463977165437478108703953"
      "975242264583527631497607121698639404463425083816458489550910690645853573"
      "049244936966036388297937396051814930823465912651170695056695684354705423"
      "095352361101726558172241626228546112263395596881499981414032212201760976"
      "520795903625575798849125176119243272558964903449212447797995245022748392"
      "449140400999893327138362946930129079489843914654316839228169929031059034"
      "459343106243738422197502632441420335664086007403838166913622595331678504"
      "926803750122514114625616566363817794226241673119948642813039705105038252"
      "221324582851289320842433595903946946021833586747115399461991296343323607"
      "311923511863564156397852902787924087534387320059914838519725897551460691"
      "621353051720109028132318400833156061998103669207972198825127167043458586"
      "639267911696352127693613084814542985336759732579984812603403661386876512"
      "785892451389522044908486961483762169089940135347407292253276131138439144"
      "731642202379516989344254250734120484450181097472911825590742879346300651"
      "233305792458155938752121281687447651698450240049324608599262375784333046"
      "364025478770054252019335797797716042816114620115147675392033419028145897"
      "577575099182021157117165481719420763957864656885623517409407756431783765"
      "369213648209359803836169478233492553954392039363495017310232945758195904"
      "189984870483251893424968044726289069993731306869090928602197278657569506"
      "238881390042794507731747533399046034415909306112200556454310531957111865"
      "376892847710377288129969695599622844850900523647125106565585762781840795"
      "552034742305725752172876071144034025574410004862959023529903756145409296"
      "269749030457726131537089769376409230137831486296794761906697355952174600"
      "587767771045202432553602654291508805511607216695711019670684197571473859"
      "314341079932709504526114588658699132764202024825815162287151763519311809"
      "247495403320409624549680459241630814089480157002845400379258032868282906"
      "381339868936136227797595403805737110999547058181894870159060197768951289"
      "859708387544859625494425956773225619747771300337886567060447778303136286"
      "484733741281802465919453732048579319565172145226525584746828228280152224"
      "288837931818707589264181208164283738942883644897875144346925960993236771"
      "272693470568003088232559054355314665214869210158414350436591824430866390"
      "143449669195756635438315871715070820030683860411696777636958423467961955"
      "220258864409260494705277102239052413172072619342014358950202829051947728"
      "721886618010199165078765291720400487818302121520781623646609096355247639"
      "848873037048240180985815976887256045280830425125639237190506705904164290"
      "782682662088899576587276612652214265831686017489641135501502281132168548"
      "289588434317409900842824705492000349508571332645935508977602413747839787"
      "547437131380255111018033572990667311069251960073469756894113570940457678"
      "609590673721873254025217242773533671028944174280084784345405037298953351"
      "845440213485351525014148849713714901187235947044306460640156567091454142"
      "458746900724034363400740630956017678360258998541487458402913180201201315"
      "448526012889961133935140484091314808045056801149761052687671338682053630"
      "231749617722019940445101081644429383616600760533516850723205483409053448"
      "141104402883919798035784683065276478491282414265252659719473334919669084"
      "269629607248288572753447342413422257673092836623919933390139475710402443"
      "892030735118995044307136246708211324391455781008936019339657274840492876"
      "428784706318106573680539584276009573650392629516076089664750417738853815"
      "185144824199998581476574471626424303331087160900733329920855609757692527"
      "099715891032302734603129862184485084516443308134929507353163532156156536"
      "252853572465536206083228382857989900425979654028338377465859551877855661"
      "990075441339956349603379400644509049017097757803251467070138692030181809"
      "410261399748067495682472495606487391033792342327615990396522420198369967"
      "707450880796622141425221786388061231289783035292319012399240535228299765"
      "657128841308154300921344484779293259387349484039278394752291700085549109"
      "038708460658430757595490709822347858845195764258545757341117461594483989"
      "179570978768139132333271923093927325359381901082987148052019749934731956"
      "268036571764653557892783009848001446741881210793297841872818830198115195"
      "276442616646767117398507989938562277357088329833198546469416651649924264"
      "843246980939862907906237884149065279549617774721339201101450903014293921"
      "928573434607898458129203816341539428611357911383573194212111919467184158"
      "221519747387616191581358000774655907431069275804580913394237456006750601"
      "533021095229576760739034702967880646414820569086510083308056635218575614"
      "028682805699392250676570845505974865560906363660964249492412900071693654"
      "605246558020589673959304108829897654845777835922898061594422135859874095"
      "297641136266509167424361517533467282131118895343583687295625068445015163"
      "062948232831326771032039835703534624843937810948975174656059648251875531"
      "240246194945966401364587696319585692407898536780686164418051581455533710"
      "938009304525437131499759618352268831093268665209295772785035248489266495"
      "796051685110522479208088602604087857402204054197982291062473540051930495"
      "840097038674038179324468903594702011544657062152503361138552941171566744"
      "519766471276133493543100064515637152302790633708838864047744129103400079"
      "540300309506019693100121269367888633783656406392839281140767099017241605"
      "664634098492727860947685240410862748009834100219862340753298111170392333"
      "599208931274892837629093514715406291131154518348993801001101833681237186"
      "334650737444487111617688959312694854733495664848009697524960689405026725"
      "593182611168999751921042762495153972371565895666142022331384450733341417"
      "828065335153730574919866993355883935514411583422775222796188864318597749"
      "144857139174906561784767400496485286565464202894987469820522474606454084"
      "857782677683445840042218831297725714446549628524852261137786463949780915"
      "839595724273973974122863239444960573085042181246161574632036087070850023"
      "231062073957383700975918334452858376148126713284262701002884390294531034"
      "761234576103854924508271211516380944598830259990509137928004136119271924"
      "310611470367343194096414708399981106283641481518029142401138357329188970"
      "092208193914330777268600405520286392999948721991374086318400026597414757"
      "546138942317684419711602489575000550004192050499178905260444155909092224"
      "215209948378626682948520910886998764881342072498660699935705586195776584"
      "457681506120582437411459898072755124180432354112594154189051593832894808"
      "121606284516853844887692488208518668975797055328839919848758109105984576"
      "230258284801412252964927235269688767748545912110062590397020849522092034"
      "317431766532437330340632013800850054131166508975172214355411314196172917"
      "164962198142579724855476665269339337258006771517202287325947855565836702"
      "424477206453474292369000623805196985500252060331867380824820406246819075"
      "558234682431630428551145072626946163583038729380789385920251268587954310"
      "741809234300564476689983267320705625924782538747235401918971855161011066"
      "741383799510436053628026534705649851596895301714559040233642671392486433"
      "486568297189703025829657628096527480052652951688660874599782823714575551"
      "730474061863360972838565443573577668113783041578165377508866917083283354"
      "867691862548888449971551079402915024787237697693658070105252049130422358"
      "254801852129948015508885182092271693319452763802335199851849601589703257"
      "375162983146997757208480768332539328110603807966361416512929016596587983"
      "354714557854986598080668413610379809488143471783504713839980575903378431"
      "045005058689441133899347651486560708538825779170122232445406161391956621"
      "860233882612061385970784367708631930542821344975974218640659585365394053"
      "733783618121564571031933344618118794131364589252680948350651384249585433"
      "236790252859429719481311768742391043385522860296917566112898818065149477"
      "948014298804445301159919608201445934929573948753918074633891058191750668"
      "412619615679749928648055915090990587586408701168729253709522331875198903"
      "554864498268287081892433829016524282325181043465711082144214035336983868"
      "649665313501059932871672197974786449134185929608311918234858067425054901"
      "985257220809692722955543035029945935781787581478794479507640417449515483"
      "797965465865519667523121949634461184235189674349032051280697733971004180"
      "776307703267230965235535433715085301535525618445889538298849325009876919"
      "199381000433550723639545262469693575037063466409256936844448354718234439"
      "688620859873844999362410310984873731830674810118842841296218765992434697"
      "064747790821600623181455778599113077131058414798580097237163465604631967"
      "748917404750491517018174545336529477165379227847390958418230567940109448"
      "229710499984072045466447492635230156270059542794544514687495422366703373"
      "494941546565858024840815724051622993649192829497309475701477265782832194"
      "050980139123791487222179607437830642059067093663931909562759064557879480"
      "675139435744508909274304942065201651994663578721458936495038759750660818"
      "508488050274200933770120979982821592599456658553057051436616336948771444"
      "700540646462833727580646982453909126589926099754389180937517500979413735"
      "883795895862692734791388867612712012993774097524370041269624872438610347"
      "299152465816962060379379213977948033956479100682338114915710743824885050"
      "432717904897665063312040438693254910221217811317666329505860399639558149"
      "996202294202175412081336543803059640664434246302073345951738043220074626"
      "637036303192302081193635414380781404295190940403968770984102697771458874"
      "742974420787133040073418984446419949575246962092081402769252045367899684"
      "049592664903259242089277551105969335367734430921938539840729295600031328"
      "656774331431877190072331829638570684303537190766772964341517342553655934"
      "309301994018660662565370489878223139236886637983685921351171063847486962"
      "136980450750652168008445921373531781308261631546416736978939361519375099"
      "413864392122900226124814113704653078942035118116101128878088288062988021"
      "657123999643076360428856624602847578098974910779007235008206116789217440"
      "080816364041557305390299476674500052174627404149463729018370649037373441"
      "012503279071971013188719331236825632946424048731075400557906711715177720"
      "991945030746553842465330139098706387987083108994688277550097299021119834"
      "804505662240370274479024479854751861375403598132580551771241268981513629"
      "251452398937569514976249268989785593222950682927654941350829997492709927"
      "825710535702611964842109527221780111779019955325895843666033072002060978"
      "776512832914165148779112167051348600194144531850644440988260458187977296"
      "188679631325299698426718461965864038827149214509204418244256559145871010"
      "116944747941222753655746717740902627286073355597724016625212251675737806"
      "606154706308222360470652939809547177100275327036547448009629083957654122"
      "313558865262681430740302407385814078810942542129287852454907824301752690"
      "359073866124783950095653306804691807305510551302976398994980588630168808"
      "148770457455785174756915074307922247621718543186123639190514654068753629"
      "499959237602506337065181734230513065296654341465639598801016995526931972"
      "189267307821360398523621631059288274432813993887257805124448571455404103"
      "178320281239467959386018081568996175651439740626405924767441408882926631"
      "352111575270573004906821036253332281765026328980994736782916550294245295"
      "028415117003528533713365403602855181131559392785186883899852548812732870"
      "935554600389579986179821961005184344749191082415282563017748312329937820"
      "014237206443222225342510602791995367650568989083486503056053029415091987"
      "986541051071302650966368407822634670691620900331078959491224091958767859"
      "853388052023183636580625420508598093236279516657545852295172442999364304"
      "989883672147029645584206430408857667820798625368164035502113457857410258"
      "796122282767464328960807607346528490280045803632123618730648836128499252"
      "710885275929910505633380246053784860819527758866629023069562631088356425"
      "696853122825112827328914356229335766969719640962095430380359145532268641"
      "412961261381232027649926925992350484128978500170360766196764295858509477"
      "155937142729804948810684339476426429526911724575622855270447307953448584"
      "255972902438928127773174802849080488641568586557376759226941124558274366"
      "365369864620485406544799379347325330281045716133815488127541883070111370"
      "744194130934340712108604895408877554307411843945078672422066859485986096"
      "666717712336743490121142112262551322028938924806233962938084034186387581"
      "824843625324074960538437744276685732267061346266322241886482149471693994"
      "515530154305202630353911750815651503259699943111246917776595192089139324"
      "874754274406556126092356778977058089487255773043802109660169202148210634"
      "040071733805983332332897915233350336680626556841666033069047344219779753"
      "375828572961660227853896529335333929947671567284934738378248109296533209"
      "257393945114316339144878424709233836342453225034254551588123535000949614"
      "723261051101377916484753311605963306241138795353152089889536126362505660"
      "704919923082697349335000313181451905388978287443827659364973429060839369"
      "189761892830671528021766956291685165941397985253177092266117230681555126"
      "880153882607727607788942014987860857039617081620610604296131347779211504"
      "282195659436658612506275401080902690208973601017300063045307761342368893"
      "342113955976780351394687330815578992668484033475279540924846109740213301"
      "913753523130736786970400734692521840823303998539461209174675647889994399"
      "503694883240368404464225820653143510407002344597798376245270968341000503"
      "599690577248554897406080453636767114354174117002363046597144586917113616"
      "755924919054440641893744502021227379981987646257300665867577550584770661"
      "502057295550426618508695001331155444677302253049948637495957818420404502"
      "639473675811624550314973100658338042602475768493674996720211781976263587"
      "471595997607600923780033824003854056680966185106865197639219470111395312"
      "176266077030537462597334360229919040659196317629002817784777562060287303"
      "272872912696033703016311789413316611987850377480238539728727672579716174"
      "427374546293302914730358916135393170916485546089694832514081958682349816"
      "801164604696854120603609494921016636127326392974659904177874234534954614"
      "589134888668738506993141897061029311068923928256855750625274768796028745"
      "105856022644974789722366636570353162045404986222379459842300238374196580"
      "088233696020620325420038214713847045675744428440739586300861454667106539"
      "935417713141629860522997735993326416839201291738532897999935655933508323"
      "081140746714322467645033830204758583153269665021243743703896032319788009"
      "385409348944214964597422174157979298997316621165626512151528149599135532"
      "313997976987493674301915810273363523470482271614210019894343502564462734"
      "215444383796051922951517915062922804990821677592126243031441818582551700"
      "656252304012511271800850524515987422493272514055469931638328564641882690"
      "676700782276409483301180562664762582236508955702633966634734128636838146"
      "598527199456951108882891321121346817655586668831562127112298283330445464"
      "861774168936890621174960111961038518087175848376862528479294837421194250"
      "307095241460823977727538658938663921709559709585881921865462702250720408"
      "609856867073529672507662401165597768449746670769012815848803367557225578"
      "247690219281560623243553587549209002692581003696603051220330577960098025"
      "472902906348851560543937657371197324650924960763001653153918519834499998"
      "567288876913659048313844657912808387461302861694258533000780276925907773"
      "572671602148606814003985895124895757160221306139598175916972592299543585"
      "472891227371007530955265922531467267170868317958985890955894067329551838"
      "328410209366227763214478143542481901207327683815981058671806994473348172"
      "210880225660889607114719538559374875857156543049830917635079893392267991"
      "194939219181072232264826982027157326219071445566717663200328156091376404"
      "213968995410591290783743877094845873604938561685246733895158381208235444"
      "559933411354097121840630465165057080880353962654448030068417087844423627"
      "678831174716820624648597617768136666215577119802102018235149341318546708"
      "710527815379838854749796950198740820550873123672322965648489664868645898"
      "524298540270002598540763909114986491544551550237748757063755655176376285"
      "845510961689191584392683551948531758564664647433403945476973671877947826"
      "113273789149975166589154740752234143410815797112881412792168513324038526"
      "939238961591526290190236386277481679122967942464942610551259554574524090"
      "095814065577478079775288998885349583720828189248960623092261480028052439"
      "316671122574305826390895566054675992511806766057967510154183857983339320"
      "822480790804210784253963784564773384315664115737319190407197409970844337"
      "589144125269559151189571209825994243326232943914351708462536674488453977"
      "989229993172974291349333080448822984906729690706056007208313894245509775"
      "946817487765604580896280930854949582425439549916032845529992316220538812"
      "769717058765123435692397146772846791132443848194474629455411508455321816"
      "930101456222145734219021602824201119646213543539189029038601750253330796"
      "544118611896095815815025020545030805744974939102757059145484662636336122"
      "070382530888803968849795835383440345289336989143120579920386981783139625"
      "263362193914831941802746674132036489225383606985253316420158580433529955"
      "625299872038317726437518863666662280160301195180654655571189534825258652"
      "839361985092365726511648008157359921281562530745280328645732527733889735"
      "269824478508649027411274571980134976111619364099089817349638013063690502"
      "888186603601696989500503796032275303348816050222837291167987842204905473"
      "493754324370129107386029955439016693437958204794777520999193471616396058"
      "991768568945516832246390778479264563767388493976927687983674478712060490"
      "448893929893819750756564230260542259658874165293321531714725279673617519"
      "246720115259390874973336258063143236004943269913093752854524978403854873"
      "480695744736862536834815176555419393164542316560782359719171553416127808"
      "831409573243937032174543359786166461706034664489059129254050051265224550"
      "918935152906386691540249961077981681439952063064556239355435970868537172"
      "576306039623954760424199706310055677229199461718343871726248114549151812"
      "501303953934324870996587226800298970830974494798103931884064358630567256"
      "003720722489180185863741518744333870648047739584797111528202751995612117"
      "195257023070121744642961503659066241492789827333155032115257900045722291"
      "980860390410868656840331387312722149376";
  auto large_number = tc.root.add_root(bigint(1) << 224000);
  b = tc.root.replace_root(b, parse_bigint_decimal(large_number_decimal));
  EXPECT_EQ(*b, *large_number);
}  // NOLINT(readability/fn_size)

}  // namespace emil::testing
