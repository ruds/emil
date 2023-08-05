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
#include <linenoise.hpp>
#include <pwd.h>
#include <sys/errno.h>
#include <unistd.h>

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>

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

namespace {

constexpr std::size_t HISTORY_LEN = 1000;

const char *get_config_dir() {
  const char *dir;
  if ((dir = getenv("XDG_CONFIG_HOME"))) return dir;
  if ((dir = getenv("HOME"))) return dir;
  return getpwuid(getuid())->pw_dir;
}

struct reporter : public emil::Reporter {
  void report_error(const emil::Location &location,
                    std::string_view text) override {
    fmt::print(stdout, "{}:{}: error: {}\n", location.filename, location.line,
               text);
  }

  void report_warning(const emil::Location &location,
                      std::string_view text) override {
    fmt::print(stdout, "{}:{}: warning: {}\n", location.filename, location.line,
               text);
  }

  void report_info(std::string_view text) override {
    std::cout << text;
    flush(std::cout);
  }

  void report_type_judgement(const emil::Location &, const emil::Expr &,
                             const emil::typing::Type &) override {}
  void report_type_judgement(const emil::Location &, std::string_view,
                             const emil::typing::TypeScheme &) override {}
};

bool read_eval_print(emil::Interpreter &interpreter) {
  static std::string line;
  bool first = true;
  bool quit;

  do {
    line.clear();
    errno = 0;
    quit = linenoise::Readline(first ? " - " : " = ", line);
    first = false;
    if (quit) {
      interpreter.reset();
      return errno == EAGAIN;
    }
    linenoise::AddHistory(line);
  } while (interpreter.process_line(std::move(line)));

  return true;
}

}  // namespace

int main(int argc, char *argv[]) {
  if (argc != 1) {
    std::cerr << "Usage: " << argv[0] << "\n";
    return 1;
  }

  const auto history_path = fmt::format("{}/.emil_history", get_config_dir());

  linenoise::SetMultiLine(true);
  linenoise::SetHistoryMaxLen(HISTORY_LEN);
  linenoise::LoadHistory(history_path.c_str());

  reporter reporter;
  emil::Interpreter interpreter{reporter};

  while (read_eval_print(interpreter)) {
  }

  linenoise::SaveHistory(history_path.c_str());
}
