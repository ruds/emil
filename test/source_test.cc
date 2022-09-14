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

#include <fmt/core.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <utf8.h>

#include <cstdlib>
#include <fstream>
#include <iterator>
#include <memory>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace emil::testing {
namespace {

struct use_stream_t {};

using iss32 = std::basic_istringstream<char32_t>;

struct TestParam {
  std::shared_ptr<iss32> stream;
  std::shared_ptr<Source<>> source;

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
  Source<>& source = *GetParam().source;
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

MATCHER_P(PeeksAt, c, "") {
  const char32_t* next = arg->peek();
  return next && *next == c;
}

MATCHER_P2(PeeksAheadAtBy, c, n, "") {
  const char32_t* next = arg->peek(n);
  return next && *next == c;
}

TEST_P(SourceTest, PeeksOne) {
  Source<>& source = *GetParam().source;
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'1'));
  EXPECT_EQ(source.advance(), '1');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'2'));
  EXPECT_EQ(source.advance(), '2');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'3'));
  EXPECT_EQ(source.advance(), '3');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'4'));
  EXPECT_EQ(source.advance(), '4');
  EXPECT_TRUE(source.at_end());

  EXPECT_FALSE(source.peek());
}

TEST_P(SourceTest, PeeksAll) {
  Source<>& source = *GetParam().source;
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAheadAtBy(U'4', 3));
  EXPECT_FALSE(source.peek(4));

  EXPECT_THAT(&source, PeeksAt(U'1'));
  EXPECT_EQ(source.advance(), '1');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'2'));
  EXPECT_EQ(source.advance(), '2');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'3'));
  EXPECT_EQ(source.advance(), '3');
  ASSERT_FALSE(source.at_end());

  EXPECT_THAT(&source, PeeksAt(U'4'));
  EXPECT_EQ(source.advance(), '4');
  EXPECT_TRUE(source.at_end());

  EXPECT_FALSE(source.peek());
}

struct GraphemeTestCase {
  const std::u32string input;
  const std::vector<std::u32string> grapheme_clusters;
  const std::string description;
};

constexpr char32_t DIV = U'÷';
constexpr char32_t MUL = U'×';

template <typename It>
char32_t parse_hex_code(It& it, It end) {
  const auto begin = it;
  char32_t c = 0;
  while (it != end) {
    if ('0' <= *it && *it <= '9') {
      c = (c << 4) + (*it++ - '0');
    } else if ('A' <= *it && *it <= 'F') {
      c = (c << 4) + (*it++ - 'A' + 10);
    } else if (distance(begin, it) < 3) {
      throw std::runtime_error("Bad unicode codepoint constant " +
                               std::string(begin, it));
    } else {
      return c;
    }
  }
  throw std::runtime_error("Line too short in unicode codepoint constant.");
}

std::optional<GraphemeTestCase> parse_line(const std::string& line) {
  if (line.empty() || line.front() == '#') return {};

  std::u32string input;
  std::u32string current_cluster;
  std::vector<std::u32string> clusters;
  auto it = begin(line);
  const auto e = end(line);

  if (utf8::next(it, e) != DIV || utf8::next(it, e) != ' ')
    throw std::runtime_error("Bad test file format - start of line.");

  while (it != e && *it != '#') {
    char32_t c = parse_hex_code(it, e);
    input += c;
    current_cluster += c;
    if (it == e || *it++ != ' ')
      throw std::runtime_error("Bad test file format - sep1");
    switch (utf8::next(it, e)) {
      case DIV:
        clusters.push_back(current_cluster);
        current_cluster.clear();
        break;

      case MUL:
        break;

      default:
        throw std::runtime_error("Bad test file format - sep2");
    }

    if (it == e || (*it != ' ' && *it != '\t'))
      throw std::runtime_error("Bad test file format - sep3");
    ++it;
  }
  if (!current_cluster.empty())
    throw std::runtime_error("Bad test file format - eol");
  return GraphemeTestCase{.input = std::move(input),
                          .grapheme_clusters = std::move(clusters),
                          .description = {it, e}};
}

TEST(SourceGraphemeClusterTest, UnicodeTestCases) {
  const char* test_data_dir = std::getenv("TEST_DATA_DIR");
  ASSERT_TRUE(test_data_dir) << "TEST_DATA_DIR must be set in the environment.";
  std::ifstream infile(fmt::format("{}/GraphemeBreakTest.txt", test_data_dir));
  std::string line;
  int lineno = 0;

  int cases = 0;
  while (std::getline(infile, line)) {
    ++lineno;
    try {
      auto tc = parse_line(line);
      if (!tc) continue;
      ++cases;
      auto s = make_source(tc->input);
      std::vector<std::u32string> clusters;
      while (!s->at_end()) clusters.push_back(next_grapheme_cluster(*s));
      EXPECT_THAT(clusters, ::testing::ContainerEq(tc->grapheme_clusters))
          << "Failed on test case " << tc->description;
    } catch (std::runtime_error& e) {
      FAIL() << "Error parsing line " << lineno << ": " << e.what();
    }
  }

  ASSERT_EQ(cases, 602) << "Expected 602 test cases in file.";
}

}  // namespace
}  // namespace emil::testing
