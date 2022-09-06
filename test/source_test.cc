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

#include "emil/source.h"

#include <gtest/gtest.h>

#include <memory>
#include <sstream>

namespace emil::testing {
namespace {

struct use_stream_t {};

using iss32 = std::basic_istringstream<char32_t>;

struct TestParam {
  std::shared_ptr<iss32> stream;
  std::shared_ptr<Source> source;

  explicit TestParam(use_stream_t)
      : stream(std::make_shared<iss32>(U"1234")),
        source(make_source(*stream)) {}
  TestParam() : source(make_source(U"1234")) {}
};

[[maybe_unused]] void PrintTo(const TestParam& t, std::ostream* out) {
  *out << (t.stream ? "stream" : "string");
}

class SourceTest : public ::testing::TestWithParam<TestParam> {};

INSTANTIATE_TEST_SUITE_P(Sources, SourceTest,
                         ::testing::Values(TestParam{},
                                           TestParam{use_stream_t{}}));

TEST_P(SourceTest, Advances) {
  Source& source = *GetParam().source;
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.advance(), '1');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.advance(), '2');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.advance(), '3');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.advance(), '4');
  EXPECT_TRUE(source.at_end());
}

TEST_P(SourceTest, PeeksOne) {
  Source& source = *GetParam().source;
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '1');
  EXPECT_EQ(source.advance(), '1');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '2');
  EXPECT_EQ(source.advance(), '2');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '3');
  EXPECT_EQ(source.advance(), '3');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '4');
  EXPECT_EQ(source.advance(), '4');
  EXPECT_TRUE(source.at_end());

  EXPECT_FALSE(source.peek());
}

TEST_P(SourceTest, PeeksAll) {
  Source& source = *GetParam().source;
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(3), '4');
  EXPECT_FALSE(source.peek(4));

  EXPECT_EQ(source.peek(), '1');
  EXPECT_EQ(source.advance(), '1');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '2');
  EXPECT_EQ(source.advance(), '2');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '3');
  EXPECT_EQ(source.advance(), '3');
  ASSERT_FALSE(source.at_end());

  EXPECT_EQ(source.peek(), '4');
  EXPECT_EQ(source.advance(), '4');
  EXPECT_TRUE(source.at_end());

  EXPECT_FALSE(source.peek());
}

}  // namespace
}  // namespace emil::testing
