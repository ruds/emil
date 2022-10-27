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

#include "emil/string.h"

#include <gtest/gtest.h>

#include <string>

#include "emil/strconvert.h"
#include "testing/test_util.h"

namespace emil::testing {

TEST(ManagedStringTest, EmptyConstruction) {
  TestContext tc;
  auto ms = tc.root.add_root(make_managed<ManagedString>());
  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 0);
  EXPECT_TRUE(ms->empty());
  EXPECT_EQ(ms->size(), 0);
  EXPECT_EQ(ms->num_codepoints(), 0);
  std::u8string_view v = *ms;
  EXPECT_EQ(v, u8"");
  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 0);
}

TEST(ManagedStringTest, ShortConstruction) {
  const std::u8string expected = u8"Númenor";
  TestContext tc;
  auto ms = tc.root.add_root(make_managed<ManagedString>(expected));
  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 0);
  EXPECT_FALSE(ms->empty());
  EXPECT_EQ(ms->size(), 8);
  EXPECT_EQ(ms->num_codepoints(), 7);
  EXPECT_EQ(to_hex(*ms), "4EC3BA6D656E6F72");
  std::u8string_view v = *ms;
  EXPECT_EQ(expected, v);
  EXPECT_EQ(*ms->data(), 'N');
  EXPECT_EQ(ms->data()[3], 'm');
  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 0);
}

TEST(ManagedStringTest, LongConstruction) {
  const std::u8string lorem =
      u8"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do "
      u8"eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim "
      u8"ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut "
      u8"aliquip ex ea commodo consequat. Duis aute irure dolor in "
      u8"reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla "
      u8"pariatur. Excepteur sint occaecat cupidatat non proident, sunt in "
      u8"culpa qui officia deserunt mollit anim id est laborum.";
  const std::u8string spanish =
      u8"El veloz murciélago hindú comía feliz cardillo y kiwi. La cigüeña "
      u8"tocaba el saxofón detrás del palenque de paja.";
  const std::u8string polish = u8"Zażółć gęślą jaźń";
  const std::u8string russian =
      u8"Съешь же ещё этих мягких французских булок, да выпей чаю";
  TestContext tc;
  auto mlorem = tc.root.add_root(make_managed<ManagedString>(lorem));
  auto mspanish = tc.root.add_root(make_managed<ManagedString>(spanish));
  auto mpolish = tc.root.add_root(make_managed<ManagedString>(polish));
  auto mrussian = tc.root.add_root(make_managed<ManagedString>(russian));

  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 4);

  EXPECT_FALSE(mlorem->empty());
  EXPECT_EQ(mlorem->size(), lorem.size());
  EXPECT_EQ(mlorem->num_codepoints(), lorem.size());
  EXPECT_EQ(static_cast<std::u8string_view>(*mlorem), lorem);

  EXPECT_FALSE(mspanish->empty());
  EXPECT_EQ(mspanish->size(), spanish.size());
  EXPECT_EQ(mspanish->num_codepoints(), 112);
  EXPECT_EQ(static_cast<std::u8string_view>(*mspanish), spanish);

  EXPECT_FALSE(mpolish->empty());
  EXPECT_EQ(mpolish->size(), polish.size());
  EXPECT_EQ(mpolish->num_codepoints(), 17);
  EXPECT_EQ(static_cast<std::u8string_view>(*mpolish), polish);

  EXPECT_FALSE(mrussian->empty());
  EXPECT_EQ(mrussian->size(), russian.size());
  EXPECT_EQ(mrussian->num_codepoints(), 56);
  EXPECT_EQ(static_cast<std::u8string_view>(*mrussian), russian);

  EXPECT_EQ(tc.mgr.stats().num_private_buffers, 4);
}

TEST(ManagedStringTest, Comparison) {
  const std::u8string a = u8"aaa";
  const std::u8string b = u8"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
  const std::u8string c = u8"cccccccccccccccccccccccccccccccccc";
  const std::u8string d = u8"ddd";
  TestContext tc;
  auto ma = tc.root.add_root(make_string(a));
  auto ma2 = tc.root.add_root(make_string(a));
  auto mb = tc.root.add_root(make_string(b));
  auto mc = tc.root.add_root(make_string(c));
  auto mc2 = tc.root.add_root(make_string(c));
  auto md = tc.root.add_root(make_string(d));

  // Two short strings (a and d) and two long strings (b and c).
  // We'll check the reflexive relationships for a and c, and binary
  // relationships for a/b, a/d, b/c, and b/d.

  EXPECT_EQ(mc, mc);
  EXPECT_NE(mc, mc2);

  // a reflexive
  EXPECT_TRUE(a == *ma);
  EXPECT_TRUE(*ma == a);
  EXPECT_TRUE(*ma == *ma);

  EXPECT_FALSE(a != *ma);
  EXPECT_FALSE(*ma != a);
  EXPECT_FALSE(*ma != *ma);

  EXPECT_FALSE(a < *ma);
  EXPECT_FALSE(*ma < a);
  EXPECT_FALSE(*ma < *ma);

  EXPECT_TRUE(a <= *ma);
  EXPECT_TRUE(*ma <= a);
  EXPECT_TRUE(*ma <= *ma);

  EXPECT_FALSE(a > *ma);
  EXPECT_FALSE(*ma > a);
  EXPECT_FALSE(*ma > *ma);

  EXPECT_TRUE(a >= *ma);
  EXPECT_TRUE(*ma >= a);
  EXPECT_TRUE(*ma >= *ma);

  EXPECT_EQ(ma, ma);
  EXPECT_NE(ma, ma2);

  EXPECT_TRUE(*ma == *ma2);
  EXPECT_FALSE(*ma != *ma2);
  EXPECT_FALSE(*ma < *ma2);
  EXPECT_TRUE(*ma <= *ma2);
  EXPECT_FALSE(*ma > *ma2);
  EXPECT_TRUE(*ma >= *ma2);

  // c reflexive
  EXPECT_TRUE(c == *mc);
  EXPECT_TRUE(*mc == c);
  EXPECT_TRUE(*mc == *mc);

  EXPECT_FALSE(c != *mc);
  EXPECT_FALSE(*mc != c);
  EXPECT_FALSE(*mc != *mc);

  EXPECT_FALSE(c < *mc);
  EXPECT_FALSE(*mc < c);
  EXPECT_FALSE(*mc < *mc);

  EXPECT_TRUE(c <= *mc);
  EXPECT_TRUE(*mc <= c);
  EXPECT_TRUE(*mc <= *mc);

  EXPECT_FALSE(c > *mc);
  EXPECT_FALSE(*mc > c);
  EXPECT_FALSE(*mc > *mc);

  EXPECT_TRUE(c >= *mc);
  EXPECT_TRUE(*mc >= c);
  EXPECT_TRUE(*mc >= *mc);

  EXPECT_EQ(mc, mc);
  EXPECT_NE(mc, mc2);

  EXPECT_TRUE(*mc == *mc2);
  EXPECT_FALSE(*mc != *mc2);
  EXPECT_FALSE(*mc < *mc2);
  EXPECT_TRUE(*mc <= *mc2);
  EXPECT_FALSE(*mc > *mc2);
  EXPECT_TRUE(*mc >= *mc2);

  // a/b binary
  EXPECT_FALSE(*ma == *mb);
  EXPECT_FALSE(*ma == b);
  EXPECT_FALSE(a == *mb);
  EXPECT_FALSE(*mb == *ma);
  EXPECT_FALSE(*mb == a);
  EXPECT_FALSE(b == *ma);

  EXPECT_TRUE(*ma != *mb);
  EXPECT_TRUE(*ma != b);
  EXPECT_TRUE(a != *mb);
  EXPECT_TRUE(*mb != *ma);
  EXPECT_TRUE(*mb != a);
  EXPECT_TRUE(b != *ma);

  EXPECT_TRUE(*ma < *mb);
  EXPECT_TRUE(*ma < b);
  EXPECT_TRUE(a < *mb);
  EXPECT_FALSE(*mb < *ma);
  EXPECT_FALSE(*mb < a);
  EXPECT_FALSE(b < *ma);

  EXPECT_TRUE(*ma <= *mb);
  EXPECT_TRUE(*ma <= b);
  EXPECT_TRUE(a <= *mb);
  EXPECT_FALSE(*mb <= *ma);
  EXPECT_FALSE(*mb <= a);
  EXPECT_FALSE(b <= *ma);

  EXPECT_FALSE(*ma > *mb);
  EXPECT_FALSE(*ma > b);
  EXPECT_FALSE(a > *mb);
  EXPECT_TRUE(*mb > *ma);
  EXPECT_TRUE(*mb > a);
  EXPECT_TRUE(b > *ma);

  EXPECT_FALSE(*ma >= *mb);
  EXPECT_FALSE(*ma >= b);
  EXPECT_FALSE(a >= *mb);
  EXPECT_TRUE(*mb >= *ma);
  EXPECT_TRUE(*mb >= a);
  EXPECT_TRUE(b >= *ma);

  // a/d binary
  EXPECT_FALSE(*ma == *md);
  EXPECT_FALSE(*ma == d);
  EXPECT_FALSE(a == *md);
  EXPECT_FALSE(*md == *ma);
  EXPECT_FALSE(*md == a);
  EXPECT_FALSE(d == *ma);

  EXPECT_TRUE(*ma != *md);
  EXPECT_TRUE(*ma != d);
  EXPECT_TRUE(a != *md);
  EXPECT_TRUE(*md != *ma);
  EXPECT_TRUE(*md != a);
  EXPECT_TRUE(d != *ma);

  EXPECT_TRUE(*ma < *md);
  EXPECT_TRUE(*ma < d);
  EXPECT_TRUE(a < *md);
  EXPECT_FALSE(*md < *ma);
  EXPECT_FALSE(*md < a);
  EXPECT_FALSE(d < *ma);

  EXPECT_TRUE(*ma <= *md);
  EXPECT_TRUE(*ma <= d);
  EXPECT_TRUE(a <= *md);
  EXPECT_FALSE(*md <= *ma);
  EXPECT_FALSE(*md <= a);
  EXPECT_FALSE(d <= *ma);

  EXPECT_FALSE(*ma > *md);
  EXPECT_FALSE(*ma > d);
  EXPECT_FALSE(a > *md);
  EXPECT_TRUE(*md > *ma);
  EXPECT_TRUE(*md > a);
  EXPECT_TRUE(d > *ma);

  EXPECT_FALSE(*ma >= *md);
  EXPECT_FALSE(*ma >= d);
  EXPECT_FALSE(a >= *md);
  EXPECT_TRUE(*md >= *ma);
  EXPECT_TRUE(*md >= a);
  EXPECT_TRUE(d >= *ma);

  // b/c binary
  EXPECT_FALSE(*mb == *mc);
  EXPECT_FALSE(*mb == c);
  EXPECT_FALSE(b == *mc);
  EXPECT_FALSE(*mc == *mb);
  EXPECT_FALSE(*mc == b);
  EXPECT_FALSE(c == *mb);

  EXPECT_TRUE(*mb != *mc);
  EXPECT_TRUE(*mb != c);
  EXPECT_TRUE(b != *mc);
  EXPECT_TRUE(*mc != *mb);
  EXPECT_TRUE(*mc != b);
  EXPECT_TRUE(c != *mb);

  EXPECT_TRUE(*mb < *mc);
  EXPECT_TRUE(*mb < c);
  EXPECT_TRUE(b < *mc);
  EXPECT_FALSE(*mc < *mb);
  EXPECT_FALSE(*mc < b);
  EXPECT_FALSE(c < *mb);

  EXPECT_TRUE(*mb <= *mc);
  EXPECT_TRUE(*mb <= c);
  EXPECT_TRUE(b <= *mc);
  EXPECT_FALSE(*mc <= *mb);
  EXPECT_FALSE(*mc <= b);
  EXPECT_FALSE(c <= *mb);

  EXPECT_FALSE(*mb > *mc);
  EXPECT_FALSE(*mb > c);
  EXPECT_FALSE(b > *mc);
  EXPECT_TRUE(*mc > *mb);
  EXPECT_TRUE(*mc > b);
  EXPECT_TRUE(c > *mb);

  EXPECT_FALSE(*mb >= *mc);
  EXPECT_FALSE(*mb >= c);
  EXPECT_FALSE(b >= *mc);
  EXPECT_TRUE(*mc >= *mb);
  EXPECT_TRUE(*mc >= b);
  EXPECT_TRUE(c >= *mb);

  // b/d binary
  EXPECT_FALSE(*mb == *md);
  EXPECT_FALSE(*mb == d);
  EXPECT_FALSE(b == *md);
  EXPECT_FALSE(*md == *mb);
  EXPECT_FALSE(*md == b);
  EXPECT_FALSE(d == *mb);

  EXPECT_TRUE(*mb != *md);
  EXPECT_TRUE(*mb != d);
  EXPECT_TRUE(b != *md);
  EXPECT_TRUE(*md != *mb);
  EXPECT_TRUE(*md != b);
  EXPECT_TRUE(d != *mb);

  EXPECT_TRUE(*mb < *md);
  EXPECT_TRUE(*mb < d);
  EXPECT_TRUE(b < *md);
  EXPECT_FALSE(*md < *mb);
  EXPECT_FALSE(*md < b);
  EXPECT_FALSE(d < *mb);

  EXPECT_TRUE(*mb <= *md);
  EXPECT_TRUE(*mb <= d);
  EXPECT_TRUE(b <= *md);
  EXPECT_FALSE(*md <= *mb);
  EXPECT_FALSE(*md <= b);
  EXPECT_FALSE(d <= *mb);

  EXPECT_FALSE(*mb > *md);
  EXPECT_FALSE(*mb > d);
  EXPECT_FALSE(b > *md);
  EXPECT_TRUE(*md > *mb);
  EXPECT_TRUE(*md > b);
  EXPECT_TRUE(d > *mb);

  EXPECT_FALSE(*mb >= *md);
  EXPECT_FALSE(*mb >= d);
  EXPECT_FALSE(b >= *md);
  EXPECT_TRUE(*md >= *mb);
  EXPECT_TRUE(*md >= b);
  EXPECT_TRUE(d >= *mb);
}

}  // namespace emil::testing
