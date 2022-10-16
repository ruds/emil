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

#pragma once

#include <gmpxx.h>

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace emil::astprinter {

void print_ast(std::string& out, int, std::string_view arg);
void print_ast(std::string& out, int, const char* arg);
void print_ast(std::string& out, int, const mpz_class& arg);
void print_ast(std::string& out, int, bool arg);
void print_ast(std::string& out, int, int64_t arg);
void print_ast(std::string& out, int, double arg);
void print_ast(std::string& out, int, const std::u8string& arg);
void print_ast(std::string& out, int, char32_t arg);

template <typename T>
void print_ast(std::string& out, int indent, const std::unique_ptr<T>& arg) {
  print_ast(*arg, out, indent);
}

template <typename K, typename V>
void print_ast(std::string& out, int indent, const std::pair<K, V>& arg) {
  std::string joiner(indent + 2, ' ');
  joiner = "\n" + joiner;
  out += '(';
  print_ast(out, indent, arg.first);
  out.append(joiner);
  out.append(". ");
  print_ast(out, indent + 4, arg.second);
  out += ')';
}

template <typename T>
void print_ast(std::string& out, int indent, const std::vector<T>& arg) {
  if (arg.size() == 0) {
    out.append("()");
    return;
  }
  if (arg.size() == 1) {
    out += '(';
    print_ast(out, indent, arg[0]);
    out += ')';
    return;
  }
  out += '(';
  std::string joiner(indent + 4, ' ');
  joiner = "\n" + joiner;
  for (const auto& a : arg) {
    out.append(joiner);
    print_ast(out, indent + 4, a);
  }
  out.append(joiner.data(), indent + 1);
  out += ')';
}

void print_ast_joined(std::string& out, int indent, const std::string&,
                      const auto& arg) {
  print_ast(out, indent, arg);
}

void print_ast_joined(std::string& out, int indent, const std::string& joiner,
                      const auto& first, const auto&... rest) {
  print_ast(out, indent, first);
  out.append(joiner);
  print_ast_joined(out, indent, joiner, rest...);
}

void print_sexp(std::string& out, int indent, const auto&... args) {
  std::string joiner(indent + 4, ' ');
  joiner = "\n" + joiner;
  out += '(';
  print_ast_joined(out, indent + 4, joiner, args...);
  out += ')';
}

}  // namespace emil::astprinter
