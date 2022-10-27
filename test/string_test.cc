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

}  // namespace emil::testing
