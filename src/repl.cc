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
#include <fmt/ostream.h>
#include <linenoise.hpp>
#include <pwd.h>
#include <sys/errno.h>
#include <unistd.h>
#include <utf8.h>

#include <cassert>
#include <coroutine>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "emil/ast.h"
#include "emil/lexer.h"
#include "emil/parser.h"
#include "emil/processor.h"

constexpr std::size_t HISTORY_LEN = 1000;

const char *get_config_dir() {
  const char *dir;
  if ((dir = getenv("XDG_CONFIG_HOME"))) return dir;
  if ((dir = getenv("HOME"))) return dir;
  return getpwuid(getuid())->pw_dir;
}

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

int main(int argc, char *argv[]) {
  if (argc != 1) {
    std::cerr << "Usage: " << argv[0] << "\n";
    return 1;
  }

  const auto history_path = fmt::format("{}/.emil_history", get_config_dir());

  linenoise::SetMultiLine(true);
  linenoise::SetHistoryMaxLen(HISTORY_LEN);
  linenoise::LoadHistory(history_path.c_str());

  emil::lexer lexer("<stdin>");
  emil::parser parser;
  auto nodes = convert_lines() | lexer.lex() | parser.parse();
  std::vector<std::unique_ptr<emil::TopDecl>> batch;
  while (true) {
    assert(!lexer.requires_more_input());
    batch.clear();

    std::string line;
    errno = 0;
    auto quit = linenoise::Readline(" - ", line);
    if (quit) {
      if (errno == EAGAIN) continue;
      break;
    }
    nodes.process(line);
    linenoise::AddHistory(std::move(line));

    try {
      while (nodes)
        batch.push_back(emil::processor::get_value_or_throw(nodes()));

      while (lexer.requires_more_input() || parser.requires_more_input()) {
        std::string continuation;
        errno = 0;
        quit = linenoise::Readline(" = ", continuation);
        if (quit) break;
        nodes.process(continuation);
        linenoise::AddHistory(std::move(continuation));

        while (nodes)
          batch.push_back(emil::processor::get_value_or_throw(nodes()));
      }
    } catch (emil::LexingError &err) {
      std::cout << err.what() << std::endl;
      continue;
    } catch (emil::ParsingError &err) {
      std::cout << err.what() << std::endl;
      nodes.reset();
      while (nodes) nodes();
      continue;
    }
    if (quit) {
      if (errno == EAGAIN) {
        nodes.reset();
        while (nodes) nodes();
        continue;
      }
      break;
    }

    for (const auto &t : batch) {
      fmt::print(std::cout, "{} ", print_ast(*t, 0));
    }
    std::cout << std::endl;
  }

  linenoise::SaveHistory(history_path.c_str());
}
