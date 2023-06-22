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

#include <cstdlib>
#include <iostream>
#include <string>
#include <utility>

constexpr std::size_t HISTORY_LEN = 1000;

const char *get_config_dir() {
  const char *dir;
  if ((dir = getenv("XDG_CONFIG_HOME"))) return dir;
  if ((dir = getenv("HOME"))) return dir;
  return getpwuid(getuid())->pw_dir;
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

  while (true) {
    std::string line;
    errno = 0;
    auto quit = linenoise::Readline(" - ", line);
    if (quit) {
      if (errno == EAGAIN) continue;
      break;
    }
    std::cout << "echo: " << line << std::endl;
    linenoise::AddHistory(std::move(line));
  }

  linenoise::SaveHistory(history_path.c_str());
}
