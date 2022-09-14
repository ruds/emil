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
   * Each element is a string "TYPE NAME".
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

const std::vector<AstNodeSpec> EXPRESSIONS{
    {"BigintLiteral", {"mpz_class val"}},
    {"IntLiteral", {"int64_t =val"}},
    {"FpLiteral", {"double =val"}},
    {"StringLiteral", {"str val"}},
    {"CharLiteral", {"char32_t =val"}},
    {"FstringLiteral", {"[str] segments", "[Expr*] substitutions"}},
};

const std::vector<AstNodeSpec> DECLARATIONS{{"Val", {"str id", "Expr* val"}}};

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

namespace emil {
%EXPR_FWD_DECLS%

class Expr {
 public:
  class Visitor {
   public:
    virtual ~Visitor();
%EXPR_V_FUNCS%
  };

  virtual ~Expr();

  virtual void accept(Visitor& visitor) const = 0;
};
%EXPR_DECLS%
%DECL_FWD_DECLS%

class Decl {
 public:
  class Visitor {
   public:
    virtual ~Visitor();
%DECL_V_FUNCS%
  };

  virtual ~Decl();

  virtual void accept(Visitor& visitor) const = 0;
};

%DECL_DECLS%

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

namespace emil {

Expr::~Expr() = default;
Expr::Visitor::~Visitor() = default;
%EXPR_IMPLS%
Decl::~Decl() = default;
Decl::Visitor::~Visitor() = default;
%DECL_IMPLS%

}  // namespace emil
)";

const std::string FWD_DECL_TEMPLATE = R"(
class %NAME%;)";

const std::string VISITOR_FUNC_TEMPLATE = R"(
    virtual void visit%NAME%(const %NAME%& node) = 0;)";

const std::string DECL_TEMPLATE = R"(
class %NAME% : public %BASE% {
 public:
  %NAME%(%FIELDLIST%);
  ~%NAME%() override;

  void accept(Visitor& visitor) const override;

 private:
%FIELDS%
};
)";

const std::string IMPL_TEMPLATE = R"(
%NAME%::%NAME%(%FIELDLIST%)
  : %INITIALIZERS% {}

%NAME%::~%NAME%() = default;

void %NAME%::accept(Visitor& visitor) const {
  visitor.visit%NAME%(*this);
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
  std::ostringstream field_list;
  auto field_list_out =
      std::experimental::make_ostream_joiner(field_list, ",\n    ");
  std::ostringstream fields;
  auto fields_out = std::experimental::make_ostream_joiner(fields, "\n");
  std::ostringstream initializers;
  auto initializers_out =
      std::experimental::make_ostream_joiner(initializers, ",\n    ");

  for (const auto& param : spec.params) {
    auto space = param.find(' ');
    if (space == std::string::npos || param.size() < space + 2)
      throw std::runtime_error(
          fmt::format("Param should be \"TYPE NAME\" but was {}", param));
    const auto type = transform_type(param.substr(0, space));
    const bool is_copyable = param[space + 1] == '=';
    const auto name = param.substr(space + (is_copyable ? 2 : 1));
    *field_list_out++ = fmt::format("{} {}", type, name);
    *fields_out++ = fmt::format("  {} {};", type, name);
    *initializers_out++ =
        fmt::format("{}({})", name,
                    is_copyable ? name : fmt::format("std::move({})", name));
  }

  dict["FIELDLIST"] = field_list.str();
  dict["FIELDS"] = fields.str();
  dict["INITIALIZERS"] = initializers.str();
  return dict;
}

Dict build_dict() {
  Dict dict;
  dict["COPYRIGHT"] = COPYRIGHT;

  auto expr_fwd_decls = back_inserter(dict["EXPR_FWD_DECLS"]);
  auto expr_v_funcs = back_inserter(dict["EXPR_V_FUNCS"]);
  auto expr_decls = back_inserter(dict["EXPR_DECLS"]);
  auto expr_impls = back_inserter(dict["EXPR_IMPLS"]);
  for (const auto& expr : EXPRESSIONS) {
    const Dict node_dict = build_node_dict("Expr", expr);
    expr_fwd_decls =
        populate_template(FWD_DECL_TEMPLATE, node_dict, expr_fwd_decls);
    expr_v_funcs =
        populate_template(VISITOR_FUNC_TEMPLATE, node_dict, expr_v_funcs);
    expr_decls = populate_template(DECL_TEMPLATE, node_dict, expr_decls);
    expr_impls = populate_template(IMPL_TEMPLATE, node_dict, expr_impls);
  }

  auto decl_fwd_decls = back_inserter(dict["DECL_FWD_DECLS"]);
  auto decl_v_funcs = back_inserter(dict["DECL_V_FUNCS"]);
  auto decl_decls = back_inserter(dict["DECL_DECLS"]);
  auto decl_impls = back_inserter(dict["DECL_IMPLS"]);
  for (const auto& decl : DECLARATIONS) {
    const Dict node_dict = build_node_dict("Decl", decl);
    decl_fwd_decls =
        populate_template(FWD_DECL_TEMPLATE, node_dict, decl_fwd_decls);
    decl_v_funcs =
        populate_template(VISITOR_FUNC_TEMPLATE, node_dict, decl_v_funcs);
    decl_decls = populate_template(DECL_TEMPLATE, node_dict, decl_decls);
    decl_impls = populate_template(IMPL_TEMPLATE, node_dict, decl_impls);
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
