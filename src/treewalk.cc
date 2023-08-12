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

#include "emil/treewalk.h"

#include <fmt/core.h>
#include <fmt/format.h>
#include <utf8.h>

#include <cassert>
#include <cmath>
#include <cstddef>
#include <functional>
#include <iterator>
#include <optional>
#include <stdexcept>
#include <utility>

#include "emil/bigint.h"
#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/tree.h"
#include "emil/typed_ast.h"
#include "emil/types.h"
#include "emil/value.h"

namespace emil {

namespace {

class ThrowingTypeVisitor : public typing::TypeVisitor {
 public:
  void visit(const typing::TypeWithAgeRestriction& t) final {
    t.type()->accept(*this);
  }

  void visit(const typing::TypeVar&) override {
    throw std::logic_error("Didn't expect typevar");
  }

  void visit(const typing::UndeterminedType&) override {
    throw std::logic_error("Didn't expect undetermined type");
  }

  void visit(const typing::TupleType&) override {
    throw std::logic_error("Didn't expect tuple type");
  }

  void visit(const typing::RecordType&) override {
    throw std::logic_error("Didn't expect record type");
  }

  void visit(const typing::FunctionType&) override {
    throw std::logic_error("Didn't expect function type");
  }

  void visit(const typing::ConstructedType&) override {
    throw std::logic_error("Didn't expect constructed type");
  }
};

class ValEnv : public Managed {
 public:
  static managed_ptr<ValEnv> dflt() {
    return make_managed<ValEnv>(
        collections::MapPtr<ManagedString, ManagedValue>::dflt());
  }

  std::optional<value_t> get(std::u8string_view name) const {
    return names_->get(name).transform(
        [](const managed_ptr<ManagedValue>& v) { return v->get(); });
  }

  [[nodiscard]] managed_ptr<ValEnv> assign(std::u8string_view name,
                                           value_t value, value_tag tag) const {
    return assign(make_string(name), value, tag);
  }

  [[nodiscard]] managed_ptr<ValEnv> assign(StringPtr name, value_t value,
                                           value_tag tag) const {
    return make_managed<ValEnv>(
        names_->insert(name, make_managed<ManagedValue>(value, tag)).first);
  }

  collections::MapPtr<ManagedString, ManagedValue> env() const {
    return names_;
  }

  explicit ValEnv(collections::MapPtr<ManagedString, ManagedValue> names)
      : names_(names) {}

  ValEnv() : ValEnv(collections::MapPtr<ManagedString, ManagedValue>::dflt()) {}

 private:
  collections::MapPtr<ManagedString, ManagedValue> names_;

  void visit_subobjects(const ManagedVisitor& visitor) override {
    names_.accept(visitor);
  }

  std::size_t managed_size() const noexcept override { return sizeof(ValEnv); }
};

managed_ptr<ValEnv> operator+(managed_ptr<ValEnv> l, managed_ptr<ValEnv> r) {
  assert(l);
  assert(r);
  return make_managed<ValEnv>(l->env() | r->env());
}

typing::TypePtr get_constructor_param_type(
    typing::TypePtr t, managed_ptr<typing::TypeScheme> con) {
  auto fn = get_function(con->t());
  if (!fn) return nullptr;

  if (con->bound()->empty()) return fn->param();

  auto subs = typing::Substitutions::dflt();
  typing::unification_t u;
  try {
    u = typing::unify(t, fn->result(), subs);
  } catch (typing::UnificationError& err) {
    throw std::logic_error(err.what());
  }
  assert(!subs->empty());
  return typing::apply_substitutions(
      fn->param(), subs, typing::NO_ADDITIONAL_TYPE_NAME_RESTRICTION, false);
}

std::string to_schar(char32_t c) {
  switch (c) {
    case '\\':
      return "\\\\";

    case '$':
      return "\\$";

    case '\a':
      return "\\a";

    case '\b':
      return "\\b";

    case '\f':
      return "\\f";

    case '\n':
      return "\\n";

    case '\r':
      return "\\r";

    case '\t':
      return "\\t";

    case '\v':
      return "\\v";

    case '"':
      return "\\\"";

    default: {
      if (c < 32) {
        std::string out;
        out = "\\^";
        out += c + 64;
        return out;
      }
      std::u32string cstr;
      cstr += c;
      return utf8::utf32to8(cstr);
    }
  }
}

std::string print_float(double f) {
  switch (std::fpclassify(f)) {
    case FP_INFINITE:
      return f < 0 ? "-Inf" : "Inf";
    case FP_NAN:
      return "NaN";
    default:
      return fmt::to_string(f);
  }
}

class ValuePrinter : public typing::TypeVisitor {
 public:
  std::string out;

  ValuePrinter(typing::TypePtr orig, value_t val) : ptr_(orig), val_(val) {}

  void visit(const typing::TypeWithAgeRestriction& t) override {
    ptr_ = t.type();
    ptr_->accept(*this);
  }

  void visit(const typing::TypeVar&) override {
    throw std::logic_error("Can't print value with unreified type");
  }

  void visit(const typing::UndeterminedType&) override {
    throw std::logic_error("Can't print value with unreified type");
  }

  void visit(const typing::TupleType& t) override {
    const auto& types = t.types();
    auto tup = val_.tup;
    out += '(';
    for (std::size_t i = 0; i < types->size(); ++i) {
      if (i) out += ", ";
      val_ = tup->get(i);
      ptr_ = (*types)[i];
      ptr_->accept(*this);
    }
    out += ')';
  }

  void visit(const typing::RecordType& t) override {
    std::size_t i = 0;
    auto tup = val_.tup;
    out += '{';
    for (const auto& row : *t.rows()) {
      if (i) out += ", ";
      out += to_std_string(*row.first);
      out += "=";
      val_ = tup->get(i);
      ptr_ = row.second;
      ptr_->accept(*this);
    }
    out += '}';
  }

  void visit(const typing::FunctionType&) override { out += "fn"; }

  void visit(const typing::ConstructedType& t) override {
    switch (compute_tag(ptr_)) {
      case value_tag::BOOL:
        out += val_.b ? "true" : "false";
        break;

      case value_tag::BYTE:
        out += fmt::format("{:02X}", val_.byte);
        break;

      case value_tag::INT:
        out += fmt::format("{}i", val_.i);
        break;

      case value_tag::BIGINT:
        out += val_.bi->print_value();
        break;

      case value_tag::FLOAT:
        out += print_float(val_.fl);
        break;

      case value_tag::CHAR:
        out += fmt::format("#\"{}\"", to_schar(val_.c));
        break;

      case value_tag::STRING: {
        out += '"';
        std::u8string_view s = *val_.str;
        auto b = begin(s);
        auto e = end(s);
        while (b != e) {
          out += to_schar(utf8::next(b, e));
        }
        out += '"';
        break;
      }

      case value_tag::CONSTRUCTED: {
        auto con = val_.con;
        auto it = t.constructors()->env()->begin();
        std::advance(it, con->constructor());
        out += to_std_string(*it->first);
        typing::StampGenerator stamper;
        auto param_type =
            get_constructor_param_type(ptr_, it->second->scheme());
        if (param_type) {
          if (!con->arg()) throw std::logic_error("Missing argument");
          out += ' ';
          val_ = *con->arg();
          param_type->accept(*this);
        }
        break;
      }

      case value_tag::TUPLE:
      case value_tag::FUNCTION:
      case value_tag::EXCEPTION_PACK:
        throw std::logic_error("constructed type has non-constructed tag.");
    }
  }

 private:
  typing::TypePtr ptr_;
  value_t val_;
};

struct match_result_t {
  managed_ptr<ValEnv> val_env;
  managed_ptr<ExceptionPack> pack;
};

match_result_t evaluate_match(managed_ptr<match_t> match, value_t value,
                              typing::TypePtr type) {
  match_result_t result{.val_env = ValEnv::dflt()};
  // TODO: implement this fully. For now we just bind top-level names.
  for (auto name = (*match->outcomes)[0]->bind_rule->names; name;
       name = name->cdr) {
    result.val_env =
        result.val_env->assign(name->car, value, compute_tag(type));
  }
  return result;
}

class ConstructorWithArg : public FunctionValue {
 public:
  explicit ConstructorWithArg(std::size_t con_idx) : con_idx_(con_idx) {}

  result_t apply(value_t arg, typing::TypePtr type) const override {
    value_t val;
    val.con = make_managed<ConstructedValue>(con_idx_, arg, compute_tag(type));
    return val;
  }

 private:
  const std::size_t con_idx_;

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(ConstructorWithArg);
  }
};

class ExprEvaluator : public TExpr::Visitor {
 public:
  value_t val;
  value_tag tag;

  explicit ExprEvaluator(managed_ptr<ValEnv> val_env) : val_env_(val_env) {}

  void visit(const TBigintLiteralExpr& e) override {
    val.bi = e.value;
    tag = value_tag::BIGINT;
  }

  void visit(const TIntLiteralExpr& e) override {
    val.i = e.value;
    tag = value_tag::INT;
  }

  void visit(const TFpLiteralExpr& e) override {
    val.fl = e.value;
    tag = value_tag::FLOAT;
  }

  void visit(const TStringLiteralExpr& e) override {
    val.str = e.value;
    tag = value_tag::STRING;
  }

  void visit(const TCharLiteralExpr& e) override {
    val.c = e.value;
    tag = value_tag::CHAR;
  }

  void visit(const TFstringLiteralExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TIdentifierExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TRecRowExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TRecordExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TTupleExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TSequencedExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TListExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TLetExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TApplicationExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TIfExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TCaseExpr&) override {
    throw std::logic_error("Not implemented");
  }

  void visit(const TFnExpr&) override {
    throw std::logic_error("Not implemented");
  }

 private:
  managed_ptr<ValEnv> val_env_;
};

class ConstructorDefinitionVisitor : public ThrowingTypeVisitor {
 public:
  value_t val;
  value_tag tag;

  explicit ConstructorDefinitionVisitor(std::size_t idx) : idx_(idx) {}

  void visit(const typing::FunctionType&) override {
    val.fun = make_managed<ConstructorWithArg>(idx_);
    tag = value_tag::FUNCTION;
  }

  void visit(const typing::ConstructedType&) override {
    val.con = make_managed<ConstructedValue>(idx_);
    tag = value_tag::CONSTRUCTED;
  }

 private:
  std::size_t idx_;
};

class DeclEvaluator : public TDecl::Visitor {
 public:
  managed_ptr<ValEnv> val_env;
  managed_ptr<ExceptionPack> pack;

  explicit DeclEvaluator(managed_ptr<ValEnv> val_env) : val_env(val_env) {}

  void visit(const TValDecl& d) override {
    for (const auto& b : *d.bindings) {
      ExprEvaluator v{val_env};
      b->expr->accept(v);
      auto m = evaluate_match(b->match, v.val, b->expr->type);
      if (m.pack) {
        pack = m.pack;
        return;
      }
      val_env = val_env + m.val_env;
    }
  }

  void visit(const TDtypeDecl& d) override {
    for (const auto& t : *d.env->type_env()->env()) {
      std::size_t idx = 0;
      for (const auto& con : *t.second->env()->env()) {
        ConstructorDefinitionVisitor v{idx++};
        con.second->scheme()->t()->accept(v);
        val_env = val_env->assign(con.first, v.val, v.tag);
      }
    }
  }
};

class TopdeclEvaluator : public TTopDecl::Visitor {
 public:
  managed_ptr<ValEnv> val_env;
  managed_ptr<ExceptionPack> pack;

  explicit TopdeclEvaluator(managed_ptr<ValEnv> val_env) : val_env(val_env) {}

  void visit(const TEndOfFileTopDecl&) override {}

  void visit(const TDeclTopDecl& t) override {
    DeclEvaluator v{val_env};
    for (const auto& decl : *t.decls) {
      decl->accept(v);
      if (v.pack) {
        pack = v.pack;
        return;
      }
    }
    val_env = v.val_env;
  }
};

}  // namespace

class TreewalkImpl {
 public:
  managed_ptr<ExceptionPack> evaluate(const TTopDecl& t) {
    auto hold = ctx().mgr->acquire_hold();
    TopdeclEvaluator v{val_env_};
    t.accept(v);
    if (!v.pack) val_env_ = v.val_env;
    return v.pack;
  }

  std::string print(typing::TypePtr type, const value_t& value) {
    auto hold = ctx().mgr->acquire_hold();
    ValuePrinter printer{type, value};
    type->accept(printer);
    return std::move(printer.out);
  }

  std::string print(typing::TypePtr type, std::u8string_view name) {
    auto hold = ctx().mgr->acquire_hold();
    auto value = val_env_->get(name);
    if (!value)
      throw std::logic_error(
          fmt::format("Could not find {}", to_std_string(name)));
    return print(type, *value);
  }

  void visit_root(const ManagedVisitor& visitor) { val_env_.accept(visitor); }

 private:
  managed_ptr<ValEnv> val_env_ = ValEnv::dflt();
};

Treewalk::Treewalk() : impl_(std::make_unique<TreewalkImpl>()) {}

Treewalk::~Treewalk() = default;

managed_ptr<ExceptionPack> Treewalk::evaluate(const TTopDecl& topdecl) {
  return impl_->evaluate(topdecl);
}

std::string Treewalk::print(typing::TypePtr type, const value_t& value) {
  return impl_->print(type, value);
}

std::string Treewalk::print(typing::TypePtr type, std::u8string_view name) {
  return impl_->print(type, name);
}

void Treewalk::visit_root(const ManagedVisitor& visitor) {
  impl_->visit_root(visitor);
}

}  // namespace emil
