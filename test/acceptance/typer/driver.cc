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

#include <cstdio>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>
#include <string_view>

#include "emil/gc.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/reporter.h"
#include "emil/runtime.h"
#include "emil/token.h"
#include "emil/typed_ast.h"
#include "emil/typer.h"

namespace emil::typing {
class Basis;
}

namespace emil::testing {

using OutIt = std::ostreambuf_iterator<char>;

class DriverRoot : public Root {
 public:
  void visit_root(const ManagedVisitor&) override {}
};

class DriverContextAccessor {
 public:
  static void install_context(RuntimeContext& rc) {
    ContextManager::get()->install_context(rc);
  }
};

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

 private:
  OutIt& out_;
};

void process_next_topdecl(managed_ptr<typing::Basis>& B, Typer& typer,
                          Parser& parser, OutIt& out) {
  auto topdecl = parser.next();
  auto e = typer.elaborate(B, *topdecl);
  B = e.B;
  fmt::format_to(out, "@{:04}:\n{}", e.topdecl->location.line,
                 describe_basis_updates(*e.topdecl));
}

void process_file(std::string_view infile, const std::string& outfile) {
  DriverRoot root;
  MemoryManager mgr{root};
  RuntimeContext rc{.mgr = &mgr};
  DriverContextAccessor::install_context(rc);
  auto hold = mgr.acquire_hold();

  Parser parser(emil::make_lexer(infile));

  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);
  TestReporter reporter{out};
  Typer typer{reporter};

  auto B = typer.initial_basis();

  while (!parser.at_end()) {
    try {
      process_next_topdecl(B, typer, parser, out);
    } catch (ElaborationError& e) {
      reporter.report_error(e.location, e.msg);
    }
    outstream.flush();
  }
}

}  // namespace emil::testing

int main(int argc, char* argv[]) {
  if (argc != 3) {
    fmt::print(stderr, "Usage: {} INFILE OUTFILE", argv[0]);
    return 1;
  }

  const std::string infile(argv[1]);
  const std::string outfile(argv[2]);

  emil::testing::process_file(infile, outfile);
}
