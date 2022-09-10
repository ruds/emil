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

#include <fmt/format.h>
#include <utf8.h>

#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>

#include "emil/lexer.h"
#include "emil/source.h"
#include "emil/token.h"
#include "fmt/core.h"

namespace emil {
namespace testing {

bool process_next_token(Lexer& lexer, std::ostreambuf_iterator<char>& out) {
  try {
    auto token = lexer.next_token();
    fmt::format_to(out, "{}\n", token);
    return token.type != TokenType::END_OF_FILE;
  } catch (LexingError& err) {
    std::cerr << err.full_msg << "\n"
              << utf8::utf32to8(err.partial_token_text) << "\n";
    fmt::format_to(out, "{:04} ERROR\n", err.line);
    lexer.advance_past(U"(*xx*)");
    return true;
  }
}

}  // namespace testing
}  // namespace emil

int main(int argc, char** argv) {
  if (argc != 3) {
    fmt::print(stderr, "Usage: {} INFILE OUTFILE", argv[0]);
    return 1;
  }

  const std::string infile(argv[1]);
  std::basic_ifstream<char32_t> stream(infile);
  emil::Lexer lexer(infile, emil::make_source(stream));

  const std::string outfile(argv[2]);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);

  while (emil::testing::process_next_token(lexer, out)) {
    outstream.flush();
  }
}
