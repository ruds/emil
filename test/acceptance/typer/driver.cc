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
#include <fmt/format.h>

#include <cstdio>
#include <cstring>
#include <exception>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>
#include <string_view>
#include <variant>

#include "emil/ast.h"
#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/processor.h"
#include "emil/reporter.h"
#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "emil/text_input.h"
#include "emil/token.h"
#include "emil/typed_ast.h"
#include "emil/typer.h"
#include "emil/types.h"

namespace emil::testing {

using OutIt = std::ostreambuf_iterator<char>;

class DriverRoot : public Root {
 public:
  std::unique_ptr<Typer> typer;
  managed_ptr<typing::Basis> B;
  managed_ptr<TTopDecl> last_topdecl;

  void initialize(Reporter& reporter) {
    auto hold = ctx().mgr->acquire_hold();
    typer = std::make_unique<Typer>(reporter);
    B = typer->initial_basis();
  }

  void visit_root(const ManagedVisitor& visitor) override {
    if (typer) typer->visit_root(visitor);
    if (B) B.accept(visitor);
    if (last_topdecl) last_topdecl.accept(visitor);
  }
};

class DriverContextAccessor {
 public:
  static void install_context(RuntimeContext& rc) {
    ContextManager::get()->install_context(rc);
  }
};

class TestReporter : public Reporter {
 public:
  explicit TestReporter(OutIt& out, bool enable_type_judgements)
      : out_(out), enable_type_judgements_(enable_type_judgements) {}

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

  void report_type_judgement(const Location& location, const Expr& expr,
                             const typing::Type& type) override {
    if (enable_type_judgements_) {
      fmt::print(stderr, "{}:{}: TYPE JUDGEMENT (expr): {} for {}\n",
                 location.filename, location.line,
                 to_std_string(typing::print_type(type)), print_ast(expr));
    }
  }

  void report_type_judgement(const Location& location,
                             std::string_view identifier,
                             const typing::TypeScheme& sigma) override {
    if (enable_type_judgements_) {
      fmt::print(stderr, "{}:{}: TYPE JUDGEMENT (binding): {}: ∀({}).{}\n",
                 location.filename, location.line, identifier,
                 fmt::join(*sigma.bound(), ", "),
                 to_std_string(typing::print_type(sigma.t())));
    }
  }

 private:
  OutIt& out_;
  const bool enable_type_judgements_;
};

void process_next_topdecl(DriverRoot& root, std::unique_ptr<TopDecl> topdecl,
                          Reporter& reporter, OutIt& out) {
  try {
    auto e = root.typer->elaborate(root.B, *topdecl);
    root.B = e.B;
    root.last_topdecl = e.topdecl;
    fmt::format_to(out, "@{:04}:\n{}", e.topdecl->location.line,
                   root.typer->describe_basis_updates(*e.topdecl));
  } catch (ElaborationError& e) {
    reporter.report_error(e.location, e.msg);
  }
}

void process_file(std::string infile, const std::string& outfile,
                  bool enable_type_judgement) {
  std::basic_ifstream<char32_t> instream{infile};
  auto in = read_stream(instream);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);
  TestReporter reporter{out, enable_type_judgement};

  DriverRoot root;
  MemoryManager mgr{root};
  RuntimeContext rc{.mgr = &mgr};

  DriverContextAccessor::install_context(rc);
  root.initialize(reporter);

  auto parser = lex(infile) | parse();

  in.finish();
  while (in) {
    parser.process(in());
    while (parser) {
      process_next_topdecl(root, get<0>(parser()), reporter, out);
      outstream.flush();
    }
  }
  parser.finish();
  while (parser) {
    process_next_topdecl(root, get<0>(parser()), reporter, out);
    outstream.flush();
  }
}

}  // namespace emil::testing

void print_usage(std::string_view progname) {
  fmt::print(stderr, "Usage: {} [-t] INFILE OUTFILE", progname);
}

int main(int argc, char* argv[]) {
  bool enable_type_judgement = false;
  std::string infile;
  std::string outfile;

  for (int i = 1; i < argc; ++i) {
    if (!std::strcmp(argv[i], "-t")) {
      enable_type_judgement = true;
    } else if (infile.empty()) {
      infile = argv[i];
    } else if (outfile.empty()) {
      outfile = argv[i];
    } else {
      print_usage(argv[0]);
      return 1;
    }
  }

  if (infile.empty() || outfile.empty()) {
    print_usage(argv[0]);
    return 1;
  }

  emil::testing::process_file(infile, outfile, enable_type_judgement);
}
