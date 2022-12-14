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

#include <fmt/core.h>

#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>

#include "emil/strconvert.h"
#include "emil/token.h"  // IWYU pragma: keep

namespace emil::astprinter {

void print_ast(std::string& out, int, std::string_view arg) { out.append(arg); }

void print_ast(std::string& out, int, const char* arg) { out.append(arg); }

void print_ast(std::string& out, int, const BigintLiteralData& arg) {
  fmt::format_to(std::back_inserter(out), "{}", arg);
}

void print_ast(std::string& out, int, bool arg) {
  out.append(arg ? "true" : "false");
}

void print_ast(std::string& out, int, int64_t arg) {
  out.append(std::to_string(arg));
  out += 'i';
}

void print_ast(std::string& out, int, double arg) {
  out.append(std::to_string(arg));
}

void print_ast(std::string& out, int, const std::u8string& arg) {
  out += '"';
  to_hex(arg, out);
  out += '"';
}

void print_ast(std::string& out, int, char32_t arg) {
  out += R"(#")";
  to_std_string(arg, out);
  out += '"';
}

}  // namespace emil::astprinter
