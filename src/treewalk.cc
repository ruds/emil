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

#include <cassert>
#include <cstddef>
#include <functional>
#include <iterator>
#include <optional>
#include <stdexcept>
#include <utility>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/runtime.h"
#include "emil/strconvert.h"
#include "emil/string.h"
#include "emil/tree.h"
#include "emil/types.h"
#include "emil/value.h"

namespace emil {

class TTopDecl;

namespace {

class ValEnv : public Managed {
 public:
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
    auto con = val_.con;
    auto it = t.constructors()->env()->begin();
    std::advance(it, con->constructor());
    out += to_std_string(*it->first);
    typing::StampGenerator stamper;
    auto param_type = get_constructor_param_type(ptr_, it->second->scheme());
    if (param_type) {
      if (!con->arg()) throw std::logic_error("Missing argument");
      out += ' ';
      val_ = *con->arg();
      param_type->accept(*this);
    }
  }

 private:
  typing::TypePtr ptr_;
  value_t val_;
};

}  // namespace

class TreewalkImpl {
 public:
  managed_ptr<ExceptionPack> evaluate(const TTopDecl&) {
    // XXX todo
    return nullptr;
  }

  std::string print(typing::TypePtr type, const value_t& value) {
    auto hold = ctx().mgr->acquire_hold();
    ValuePrinter printer{type, value};
    type->accept(printer);
    return std::move(printer.out);
  }

  std::string print(typing::TypePtr type, std::u8string_view name) {
    auto value = val_env_->get(name);
    if (!value)
      throw std::logic_error(
          fmt::format("Could not find {}", to_std_string(name)));
    return print(type, *value);
  }

  void visit_root(const ManagedVisitor& visitor) { val_env_.accept(visitor); }

 private:
  managed_ptr<ValEnv> val_env_;
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
