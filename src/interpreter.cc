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

#include <fmt/core.h>
#include <utf8.h>

#include <coroutine>
#include <exception>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

#include "emil/collections.h"
#include "emil/evaluator.h"
#include "emil/gc.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/processor.h"
#include "emil/reporter.h"
#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/tree.h"
#include "emil/treewalk.h"
#include "emil/typed_ast.h"
#include "emil/typer.h"
#include "emil/types.h"
#include "emil/value.h"

namespace emil {

class TopDecl;

namespace {

struct root : public Root {
  std::unique_ptr<Typer> typer;
  std::unique_ptr<Evaluator> evaluator;
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
  void initialize(RuntimeContext& rc, Reporter& reporter) {
    auto hold = rc.mgr->acquire_hold();
    typer = std::make_unique<Typer>(reporter);
    rc.builtin_types = &typer->builtins();
    evaluator = std::make_unique<Treewalk>();
    B = typer->initial_basis();
  }

  void visit_root(const ManagedVisitor& visitor) override {
    if (typer) typer->visit_root(visitor);
    if (evaluator) evaluator->visit_root(visitor);
    if (B) B.accept(visitor);
    if (current_topdecl) current_topdecl.accept(visitor);
  }
};

class DeclResultReporter : public TDecl::Visitor {
 public:
  DeclResultReporter(std::string& out, root& root) : out_(out), root_(root) {}

  void visit(const TValDecl& decl) override {
    auto it = back_inserter(out_);
    for (const auto& b : *decl.env->val_env()->env()) {
      auto type = b.second->scheme()->t();
      fmt::format_to(it, "val {} = {} : {}\n", to_std_string(*b.first),
                     root_.evaluator->print(type, *b.first),
                     to_std_string(print_type(
                         type, typing::CanonicalizeUndeterminedTypes::YES)));
    }
  }

  void visit(const TDtypeDecl& decl) override {
    describe_datatype_declarations(*decl.env->type_env(),
                                   root_.typer->stamper(), out_);
  }

 private:
  std::string& out_;
  root& root_;
};

class TopdeclResultReporter : public TTopDecl::Visitor {
 public:
  TopdeclResultReporter(std::string& out, root& root)
      : out_(out), root_(root) {}

  void visit(const TEndOfFileTopDecl&) override {}

  void visit(const TDeclTopDecl& t) override {
    for (const auto& decl : *t.decls) {
      decl->accept(decl_reporter_);
    }
  }

 private:
  std::string& out_;
  root& root_;
  DeclResultReporter decl_reporter_{out_, root_};
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
    root_.initialize(rc_, reporter_);
  }

  bool process_line(std::string line) {
    line_parser_.process(std::move(line));
    try {
      while (line_parser_) {
        auto ast = processor::get_value_or_throw(line_parser_());
        auto e = root_.typer->elaborate(root_.B, *ast);
        root_.B = e.B;
        root_.current_topdecl = e.topdecl;
        auto hold = ctx().mgr->acquire_hold();
        auto exc = root_.evaluator->evaluate(*e.topdecl);
        reporter_.report_info(exc ? report_results(*exc)
                                  : report_results(*e.topdecl));
      }
    } catch (LexingError& e) {
      reporter_.report_error(e.location, e.msg);
    } catch (ParsingError& e) {
      reporter_.report_error(e.location, e.msg);
      reset();
    } catch (ElaborationError& e) {
      reporter_.report_error(e.location, e.msg);
      reset();
    }
    return lexer_.requires_more_input() || parser_.requires_more_input();
  }

  void reset() {
    line_parser_.reset();
    while (line_parser_) line_parser_();
  }

  std::string report_results(const TTopDecl& topdecl) {
    std::string out;
    TopdeclResultReporter r{out, root_};
    topdecl.accept(r);
    return out;
  }

  std::string report_results(const ExceptionPack& exc) {
    return fmt::format(
        "uncaught exception {} {}\n  raised at: {}:{}",
        to_std_string(exc.constructor()),
        exc.arg() ? root_.evaluator->print(exc.arg_type(), *exc.arg()) : "",
        exc.location().filename, exc.location().line);
  }

 private:
  Reporter& reporter_;
  std::unique_ptr<Evaluator> evaluator_;
  root root_;
  MemoryManager mgr_{root_};
  RuntimeContext rc_{.mgr = &mgr_, .builtin_types = nullptr};
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

void Interpreter::reset() { impl_->reset(); }

}  // namespace emil
