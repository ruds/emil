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

#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>

#include "emil/ast.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/token.h"

namespace emil::testing {

void process_next_topdecl(Parser& parser, std::ostreambuf_iterator<char>& out) {
  try {
    auto d = parser.next();
    fmt::format_to(out, "{:04} {}\n", d->location.line, print_ast(*d, 5));
  } catch (ParsingError& err) {
    std::cerr << err.full_msg << "\n";
    fmt::format_to(out, "{:04} ERROR\n", err.location.line);
  }
}

}  // namespace emil::testing

int main(int argc, char* argv[]) {
  if (argc != 3) {
    fmt::print(stderr, "Usage: {} INFILE OUTFILE", argv[0]);
    return 1;
  }

  const std::string infile(argv[1]);
  emil::Parser parser(emil::make_lexer(infile));

  const std::string outfile(argv[2]);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);

  while (!parser.at_end()) {
    emil::testing::process_next_topdecl(parser, out);
    outstream.flush();
  }
}
