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

#include "private/ast_printer.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "emil/ast.h"

namespace emil::astprinter {

void print_ast(std::string& out, int indent, std::string_view arg) {
  out.append(arg);
}

void print_ast(std::string& out, int indent, const char* arg) {
  out.append(arg);
}

void print_ast(std::string& out, int indent, const mpz_class& arg) {
  out.append(arg.get_str());
}

void print_ast(std::string& out, int indent, bool arg) {
  out.append(arg ? "true" : "false");
}

void print_ast(std::string& out, int indent, int64_t arg) {
  out.append(std::to_string(arg));
  out += 'i';
}

void print_ast(std::string& out, int indent, double arg) {
  out.append(std::to_string(arg));
}

void print_ast(std::string& out, int indent, const std::u8string& arg) {
  out += '"';
  auto it = back_inserter(out);
  for (char8_t c : arg) {
    fmt::format_to(it, "{:02X}", (unsigned int)c);
  }
  out += '"';
}

void print_ast(std::string& out, int indent, char32_t arg) {
  if (arg < 0x10000) {
    out.append(fmt::format(R"(#"\u{:04X}")", static_cast<std::uint32_t>(arg)));
  } else {
    out.append(fmt::format(R"(#"\U{:06X}")", static_cast<std::uint32_t>(arg)));
  }
}

void print_ast(std::string& out, int indent, const std::unique_ptr<Expr>& arg) {
  print_ast(*arg, out, indent);
}

}  // namespace emil::astprinter
