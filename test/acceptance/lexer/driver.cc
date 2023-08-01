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

#include <fmt/core.h>
#include <utf8.h>

#include <cassert>
#include <cstdio>
#include <cstring>
#include <exception>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <string_view>
#include <variant>

#include "emil/lexer.h"
#include "emil/processor.h"
#include "emil/source.h"
#include "emil/text_input.h"
#include "emil/token.h"

namespace emil {
namespace testing {

template <typename NextTokenFunc>
bool process_next_token(NextTokenFunc&& next_token,
                        std::ostreambuf_iterator<char>& out) {
  try {
    auto token = next_token();
    fmt::format_to(out, "{}\n", token);
    return token.type != TokenType::END_OF_FILE;
  } catch (LexingError& err) {
    std::cerr << err.full_msg << "\n"
              << utf8::utf32to8(err.partial_token_text) << "\n";
    fmt::format_to(out, "{:04} ERROR\n", err.location.line);
    return true;
  }
}

}  // namespace testing
}  // namespace emil

namespace {

void print_usage(std::string_view program) {
  fmt::print(stderr, "Usage: {} (source|processor) INFILE OUTFILE", program);
}

}  // namespace

int main(int argc, char* argv[]) {
  if (argc != 4) {
    print_usage(argv[0]);
    return 1;
  }

  const std::string infile(argv[2]);
  std::basic_ifstream<char32_t> stream(infile);

  const std::string outfile(argv[3]);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);

  if (!std::strcmp(argv[1], "source")) {
    emil::Lexer lexer(infile, emil::make_source(stream));

    while (emil::testing::process_next_token(
        [&lexer]() {
          try {
            return lexer.next_token();
          } catch (emil::LexingError&) {
            lexer.advance_past(U"\n");
            throw;
          }
        },
        out)) {
      outstream.flush();
    }
  } else if (!std::strcmp(argv[1], "processor")) {
    auto p = emil::read_stream(stream) | emil::lex(infile);
    p.finish();
    while (emil::testing::process_next_token(
        [&p]() {
          assert(p);
          return emil::processor::get_value_or_throw(p());
        },
        out)) {
      outstream.flush();
    }
  } else {
    print_usage(argv[0]);
    return 2;
  }
}
