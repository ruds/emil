// Copyright 2023 Matt Rudary

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

#include <algorithm>
#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>
#include <string_view>

#include "emil/interpreter.h"
#include "emil/reporter.h"
#include "emil/token.h"

namespace emil {
class Expr;
namespace typing {
class Type;
class TypeScheme;
}  // namespace typing
}  // namespace emil

namespace emil::testing {

using OutIt = std::ostreambuf_iterator<char>;

class TestReporter : public Reporter {
 public:
  explicit TestReporter(OutIt& out) : out_(out) {}

  void report_error(const Location& location, std::string_view text) override {
    fmt::format_to(out_, "@{:04}: ERROR\n", location.line);
    fmt::print(stderr, "{}:{}: ERROR: {}\n", location.filename, location.line,
               text);
  }

  void report_warning(const Location& location,
                      std::string_view text) override {
    fmt::format_to(out_, "@{:04}: WARNING\n", location.line);
    fmt::print(stderr, "{}:{}: WARNING: {}\n", location.filename, location.line,
               text);
  }

  void report_info(std::string_view text) override {
    std::copy(begin(text), end(text), out_);
  }

  void report_type_judgement(const Location&, const Expr&,
                             const typing::Type&) override {}

  void report_type_judgement(const Location&, std::string_view,
                             const typing::TypeScheme&) override {}

 private:
  OutIt& out_;
};

}  // namespace emil::testing

void print_usage(std::string_view progname) {
  fmt::print(stderr, "Usage: {} INFILE OUTFILE", progname);
}

int main(int argc, char* argv[]) {
  if (argc != 3) {
    print_usage(argv[0]);
    return 1;
  }
  std::string infile = argv[1];
  std::string outfile = argv[2];

  if (infile.empty() || outfile.empty()) {
    print_usage(argv[0]);
    return 2;
  }

  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);
  emil::testing::TestReporter reporter{out};
  emil::Interpreter interpreter{reporter};

  std::ifstream instream{infile};
  std::string line;
  while (std::getline(instream, line)) {
    interpreter.process_line(line);
  }
}
