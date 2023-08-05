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

#include "emil/interpreter.h"

#include <utf8.h>

#include <coroutine>
#include <exception>
#include <iterator>
#include <string>
#include <utility>
#include <variant>

#include "emil/gc.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/processor.h"
#include "emil/reporter.h"
#include "emil/runtime.h"
#include "emil/token.h"
#include "emil/typed_ast.h"
#include "emil/typer.h"

namespace emil {

class TopDecl;
namespace typing {
class Basis;
}

namespace {

struct root : public Root {
  std::unique_ptr<Typer> typer;
  managed_ptr<typing::Basis> B;
  managed_ptr<TTopDecl> current_topdecl;

  /**
   * Initialize this root.
   *
   * There's a circular dependency between the root and the garbage
   * collector, so we construct the root first with empty pointers to
   * root objects, then initialize them once the garbage collector is
   * up and running.
   */
  void initialize(Reporter& reporter) {
    auto hold = ctx().mgr->acquire_hold();
    typer = std::make_unique<Typer>(reporter);
    B = typer->initial_basis();
  }

  void visit_root(const ManagedVisitor& visitor) override {
    if (typer) typer->visit_root(visitor);
    if (B) B.accept(visitor);
    if (current_topdecl) current_topdecl.accept(visitor);
  }
};

emil::processor::processor<std::string, char32_t> convert_lines() {
  bool needs_reset = false;
  while (true) {
    try {
      if (needs_reset) {
        needs_reset = false;
        co_yield U'\n';
      }
      auto line = co_await emil::processor::next_input{};
      auto it = begin(line);
      while (it != end(line)) {
        co_yield utf8::next(it, end(line));
      }
      co_yield U'\n';
    } catch (emil::processor::eof) {
    } catch (emil::processor::reset) {
      needs_reset = true;
    }
  }
}

}  // namespace

class InterpreterImpl {
 public:
  explicit InterpreterImpl(Reporter& reporter) : reporter_(reporter) {
    ContextManager::get()->install_context(rc_);
    root_.initialize(reporter_);
  }

  bool process_line(std::string line) {
    line_parser_.process(std::move(line));
    try {
      while (line_parser_) {
        auto ast = processor::get_value_or_throw(line_parser_());
        auto e = root_.typer->elaborate(root_.B, *ast);
        root_.B = e.B;
        root_.current_topdecl = e.topdecl;
        reporter_.report_info(root_.typer->describe_basis_updates(*e.topdecl));
      }
    } catch (LexingError& e) {
      reporter_.report_error(e.location, e.msg);
    } catch (ParsingError& e) {
      reporter_.report_error(e.location, e.msg);
      line_parser_.reset();
      while (line_parser_) line_parser_();
    } catch (ElaborationError& e) {
      reporter_.report_error(e.location, e.msg);
      line_parser_.reset();
      while (line_parser_) line_parser_();
    }
    return lexer_.requires_more_input() || parser_.requires_more_input();
  }

 private:
  Reporter& reporter_;
  root root_;
  MemoryManager mgr_{root_};
  RuntimeContext rc_{.mgr = &mgr_};
  lexer lexer_{"<stdin>"};
  parser parser_;
  processor::processor<std::string,
                       processor::Expected<std::unique_ptr<TopDecl>>>
      line_parser_ = convert_lines() | (lexer_.lex() | parser_.parse());
};

Interpreter::Interpreter(Reporter& reporter)
    : impl_(std::make_unique<InterpreterImpl>(reporter)) {}

Interpreter::~Interpreter() = default;

bool Interpreter::process_line(std::string line) {
  return impl_->process_line(std::move(line));
}

}  // namespace emil
