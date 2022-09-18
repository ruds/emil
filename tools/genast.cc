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

/**
 * @file genast.cc
 *
 * Generates classes for the Emil abstract syntax tree.
 */

#include <fmt/core.h>

#include <algorithm>
#include <cstdlib>
#include <experimental/iterator>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace emil::tools {

namespace {

struct AstNodeSpec {
  std::string name;
  /**
   * Each element is a string "TYPE NAME" or "TYPE NAME=DEFAULT".
   *
   * Type substitutions:
   * 1. str -> std::u8string
   * 2. [ELTYPE] -> std::vector<ELTYPE>
   * 3. PTYPE* -> std::unique_ptr<PTYPE>
   * 4. OPTTYPE? -> std::optional<OPTYPE>
   *
   * If NAME is =CNAME, then the field CNAME will be copied during
   * construction. Otherwise, the constructor will take an argument of
   * the derived type, which will then be moved into the field.
   */
  std::vector<std::string> params;
};

struct Category {
  std::string name;
  std::string cname;
  std::vector<AstNodeSpec> types;
};

const std::vector<Category> CATEGORIES{
    {"Expr",
     "EXPR",
     {
         {"BigintLiteral", {"mpz_class val"}},
         {"IntLiteral", {"int64_t =val"}},
         {"FpLiteral", {"double =val"}},
         {"StringLiteral", {"str val"}},
         {"CharLiteral", {"char32_t =val"}},
         {"FstringLiteral", {"[str] segments", "[Expr*] substitutions"}},
         {"Identifier",
          {"[str] qualifiers", "str identifier", "bool is_op",
           "bool is_prefix_op=false"}},
     }},
    {"Decl",
     "DECL",
     {
         {"Val", {"str id", "Expr* val"}},
     }},
    {"TopDecl",
     "TOPDECL",
     {
         {"Empty", {}},
         {"EndOfFile", {}},
         {"Expr", {"Expr* expr"}},
     }},
};

const std::vector<AstNodeSpec> DECLARATIONS{};

const std::string COPYRIGHT = R"(// Copyright 2022 Matt Rudary

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
)";

const std::string HEADER_TEMPLATE = R"(%COPYRIGHT%
/* This file is generated. Do not hand-edit! */

#pragma once

#include <gmpxx.h>

#include <memory>
#include <string>
#include <vector>
#include <utility>

#include "emil/token.h"

namespace emil {
%ALL_DECLS%
}  // namespace emil
)";

const std::string CC_TEMPLATE = R"(%COPYRIGHT%
/* This file is generated. Do not hand-edit! */

#include "emil/ast.h"

#include <gmpxx.h>

#include <memory>
#include <string>
#include <vector>
#include <utility>

#include "ast_printer.h"

namespace emil {
%ALL_IMPLS%
}  // namespace emil
)";

const std::string CATEGORY_DECL_TEMPLATE = R"(%FWD_DECLS%

class %BASE% {
 public:
  class Visitor {
   public:
    virtual ~Visitor();
%V_FUNCS%
  };

  Location location;

  explicit %BASE%(const Location& location);
  virtual ~%BASE%();

  virtual void accept(Visitor& visitor) const = 0;
};
%DECLS%
std::string print_ast(const %BASE%& v, int indent = 0);
void print_ast(const %BASE%& v, std::string& out, int indent = 0);

#define DECLARE_%CBASE%_V_FUNCS \%V_FUNC_DECLS%
)";

const std::string CATEGORY_IMPL_TEMPLATE = R"(
%BASE%::%BASE%(const Location& location) : location(location) {}
%BASE%::~%BASE%() = default;
%BASE%::Visitor::~Visitor() = default;

namespace {

class %BASE%Printer : public %BASE%::Visitor {
 public:
  %BASE%Printer(std::string* out, int indent) : out_(out), indent_(indent) {}
  ~%BASE%Printer() override = default;

  DECLARE_%CBASE%_V_FUNCS;

 private:
  std::string* out_;
  int indent_;
};

}

std::string print_ast(const %BASE%& v, int indent) {
  std::string out;
  print_ast(v, out, indent);
  return out;
}

void print_ast(const %BASE%& v, std::string& out, int indent) {
  %BASE%Printer printer(&out, indent);
  v.accept(printer);
}
%IMPLS%)";

const std::string FWD_DECL_TEMPLATE = R"(
class %NAME%;)";

const std::string VISITOR_FUNC_TEMPLATE = R"(
    virtual void visit%NAME%(const %NAME%& node) = 0;)";

const std::string VISITOR_FUNC_DECL_TEMPLATE = R"(
    void visit%NAME%(const %NAME%& node) override; \)";

const std::string DECL_TEMPLATE = R"(
class %NAME% : public %BASE% {
 public:
  %EXPLICIT%%NAME%(%FIELDLIST_WITH_DEFAULTS%);
  ~%NAME%() override;

  void accept(Visitor& visitor) const override;
%FIELDS%};
)";

const std::string IMPL_TEMPLATE = R"(
%NAME%::%NAME%(%FIELDLIST%)
  : %BASE%(location)%INITIALIZERS% {}

%NAME%::~%NAME%() = default;

void %NAME%::accept(Visitor& visitor) const {
  visitor.visit%NAME%(*this);
}

namespace {

void %BASE%Printer::visit%NAME%(const %NAME%& node) {
  astprinter::print_sexp(*out_, indent_, %SEXPLIST%);
}

}
)";

using Dict = std::map<std::string, std::string, std::less<>>;

template <std::output_iterator<char> It>
It populate_template(const std::string& templ, const Dict& dict, It out) {
  auto it = begin(templ);
  const auto e = end(templ);
  while (1) {
    auto n = std::find(it, e, '%');
    out = std::copy(it, n, out);
    if (n == e) return out;
    it = next(n);
    n = std::find(it, e, '%');
    if (n == e) throw std::runtime_error("Template ends mid-substitution.");
    std::string_view var{it, n};
    const auto sub = dict.find(var);
    if (sub == end(dict))
      throw std::runtime_error(fmt::format("No substitution for {}", var));
    out = std::copy(begin(sub->second), end(sub->second), out);
    it = next(n);
  }
}

const std::regex STR_RE(R"(\bstr\b)");
const std::regex VEC_RE(R"(\[(.*)\])");
const std::regex PTR_RE(R"((\w*)\*)");
const std::regex OPT_RE(R"((\w*)\?)");

std::string transform_type(std::string t) {
  t = std::regex_replace(t, STR_RE, "std::u8string");
  t = std::regex_replace(t, VEC_RE, R"(std::vector<$1>)");
  t = std::regex_replace(t, PTR_RE, R"(std::unique_ptr<$1>)");
  return std::regex_replace(t, OPT_RE, R"(std::optional<$1>)");
}

Dict build_node_dict(const std::string& base, const AstNodeSpec& spec) {
  Dict dict;
  dict["BASE"] = base;
  dict["NAME"] = spec.name + base;
  dict["EXPLICIT"] = size(spec.params) == 0 ? "explicit " : "";
  std::ostringstream field_list;
  auto field_list_out =
      std::experimental::make_ostream_joiner(field_list, ",\n    ");
  std::ostringstream field_list_with_defaults;
  auto field_list_with_defaults_out = std::experimental::make_ostream_joiner(
      field_list_with_defaults, ",\n    ");
  std::ostringstream fields;
  auto fields_out = std::experimental::make_ostream_joiner(fields, "\n");
  std::ostringstream initializers;
  auto initializers_out =
      std::experimental::make_ostream_joiner(initializers, ",\n    ");
  std::ostringstream sexp_list;
  auto sexp_list_out =
      std::experimental::make_ostream_joiner(sexp_list, ",\n      ");

  *field_list_out++ = "const Location& location";
  *field_list_with_defaults_out++ = "const Location& location";
  *sexp_list_out++ = fmt::format(R"("{}")", dict["NAME"]);
  for (const auto& param : spec.params) {
    const auto space = param.find(' ');
    if (space == std::string::npos || param.size() < space + 2)
      throw std::runtime_error(
          fmt::format("Param should be \"TYPE NAME\" but was {}", param));
    const auto type = transform_type(param.substr(0, space));
    const bool is_copyable = param[space + 1] == '=';
    const std::size_t name_start = space + (is_copyable ? 2 : 1);
    const auto equals = param.find('=', name_start);
    std::size_t name_count = param.size();
    std::string default_value;
    if (equals != std::string::npos) {
      name_count = equals - name_start;
      default_value += " = ";
      default_value += param.substr(equals + 1);
    }
    const auto name = param.substr(name_start, name_count);
    *field_list_out++ = fmt::format("{} {}", type, name);
    *field_list_with_defaults_out++ =
        fmt::format("{} {}{}", type, name, default_value);
    *fields_out++ = fmt::format("  {} {};", type, name);
    *initializers_out++ =
        fmt::format("{}({})", name,
                    is_copyable ? name : fmt::format("std::move({})", name));
    *sexp_list_out++ = fmt::format(R"(":{}")", name);
    *sexp_list_out++ = fmt::format("node.{}", name);
  }

  dict["FIELDLIST"] = field_list.str();
  dict["FIELDLIST_WITH_DEFAULTS"] = field_list_with_defaults.str();
  if (empty(spec.params)) {
    dict["INITIALIZERS"] = "";
    dict["FIELDS"] = "";
  } else {
    dict["INITIALIZERS"] = fmt::format(",\n  {}", initializers.str());
    dict["FIELDS"] = fmt::format("\n  {}\n", fields.str());
  }
  dict["SEXPLIST"] = sexp_list.str();
  return dict;
}

Dict build_category_dict(const Category& cat) {
  Dict dict;
  dict["BASE"] = cat.name;
  dict["CBASE"] = cat.cname;
  auto fwd_decls = back_inserter(dict["FWD_DECLS"]);
  auto v_funcs = back_inserter(dict["V_FUNCS"]);
  auto v_func_decls = back_inserter(dict["V_FUNC_DECLS"]);
  auto decls = back_inserter(dict["DECLS"]);
  auto impls = back_inserter(dict["IMPLS"]);
  for (const auto& t : cat.types) {
    const Dict node_dict = build_node_dict(cat.name, t);
    fwd_decls = populate_template(FWD_DECL_TEMPLATE, node_dict, fwd_decls);
    v_funcs = populate_template(VISITOR_FUNC_TEMPLATE, node_dict, v_funcs);
    v_func_decls =
        populate_template(VISITOR_FUNC_DECL_TEMPLATE, node_dict, v_func_decls);
    decls = populate_template(DECL_TEMPLATE, node_dict, decls);
    impls = populate_template(IMPL_TEMPLATE, node_dict, impls);
  }
  dict["V_FUNC_DECLS"].pop_back();
  dict["V_FUNC_DECLS"].pop_back();
  dict["V_FUNC_DECLS"].pop_back();
  return dict;
}

Dict build_dict() {
  Dict dict;
  dict["COPYRIGHT"] = COPYRIGHT;

  auto all_decls = back_inserter(dict["ALL_DECLS"]);
  auto all_impls = back_inserter(dict["ALL_IMPLS"]);

  for (const auto& cat : CATEGORIES) {
    const Dict cat_dict = build_category_dict(cat);
    all_decls = populate_template(CATEGORY_DECL_TEMPLATE, cat_dict, all_decls);
    all_impls = populate_template(CATEGORY_IMPL_TEMPLATE, cat_dict, all_impls);
  }

  return dict;
}

void generate_code(const char* header_filename, const char* cc_filename) {
  std::filesystem::path header_path(header_filename);
  std::filesystem::path cc_path(cc_filename);
  std::filesystem::create_directories(header_path.parent_path());
  std::filesystem::create_directories(cc_path.parent_path());
  std::ofstream header_file(header_path);
  std::ofstream cc_file(cc_path);
  const Dict dict = build_dict();
  populate_template(HEADER_TEMPLATE, dict,
                    std::ostreambuf_iterator(header_file));
  populate_template(CC_TEMPLATE, dict, std::ostreambuf_iterator(cc_file));
}

}  // namespace

}  // namespace emil::tools

int main(int argc, const char** argv) {
  if (argc != 3) {
    std::cerr << "Usage: " << argv[0] << " HEADER CC\n";
    std::exit(1);
  }
  emil::tools::generate_code(argv[1], argv[2]);
}
