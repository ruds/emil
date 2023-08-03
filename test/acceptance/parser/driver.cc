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
#include <cstring>
#include <exception>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <string>
#include <string_view>
#include <variant>

#include "emil/ast.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/processor.h"
#include "emil/text_input.h"
#include "emil/token.h"

namespace emil::testing {

template <typename NextTopDecl>
void process_next_topdecl(NextTopDecl&& next_topdecl,
                          std::ostreambuf_iterator<char>& out) {
  try {
    auto d = next_topdecl();
    fmt::format_to(out, "{:04} {}\n", d->location.line, print_ast(*d, 5));
  } catch (ParsingError& err) {
    std::cerr << err.full_msg << "\n";
    fmt::format_to(out, "{:04} ERROR\n", err.location.line);
  }
}

void process_decls(
    processor::processor<char32_t,
                         processor::Expected<std::unique_ptr<TopDecl>>>& parser,
    std::ostreambuf_iterator<char>& out) {
  while (parser) {
    emil::testing::process_next_topdecl(
        [&parser]() {
          try {
            return processor::get_value_or_throw(parser());
          } catch (ParsingError&) {
            parser.reset();
            throw;
          }
        },
        out);
  }
}

}  // namespace emil::testing

namespace {

void print_usage(std::string_view program) {
  fmt::print(stderr, "Usage: {} source INFILE OUTFILE", program);
}

}  // namespace

int main(int argc, char* argv[]) {
  if (argc != 4) {
    print_usage(argv[0]);
    return 1;
  }

  const std::string infile(argv[2]);

  const std::string outfile(argv[3]);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);

  if (!std::strcmp(argv[1], "processor")) {
    std::basic_ifstream<char32_t> stream(infile);
    auto in = emil::read_stream(stream);
    in.finish();
    auto parser = emil::lex(infile) | emil::parse();
    while (in) {
      parser.process(in());
      emil::testing::process_decls(parser, out);
    }
    parser.finish();
    emil::testing::process_decls(parser, out);
  } else {
    print_usage(argv[0]);
    return 2;
  }
}
