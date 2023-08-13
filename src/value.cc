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

#include "emil/value.h"

#include <iterator>
#include <map>
#include <new>
#include <stdexcept>
#include <utility>

#include "emil/gc.h"
#include "emil/runtime.h"
#include "emil/types.h"

namespace emil {

managed_ptr<bigint> value_t::bi() const { return managed_ptr<bigint>{managed}; }

void value_t::set_bi(managed_ptr<bigint> bi) { managed = bi.to_int(); }

StringPtr value_t::str() const { return StringPtr{managed}; }

void value_t::set_str(StringPtr str) { managed = str.to_int(); }

managed_ptr<TupleValue> value_t::tup() const {
  return managed_ptr<TupleValue>{managed};
}

void value_t::set_tup(managed_ptr<TupleValue> tup) { managed = tup.to_int(); }

managed_ptr<ConstructedValue> value_t::con() const {
  return managed_ptr<ConstructedValue>{managed};
}

void value_t::set_con(managed_ptr<ConstructedValue> con) {
  managed = con.to_int();
}

managed_ptr<FunctionValue> value_t::fun() const {
  return managed_ptr<FunctionValue>{managed};
}

void value_t::set_fun(managed_ptr<FunctionValue> fun) {
  managed = fun.to_int();
}

managed_ptr<ExceptionPack> value_t::pack() const {
  return managed_ptr<ExceptionPack>{managed};
}

void value_t::set_pack(managed_ptr<ExceptionPack> pack) {
  managed = pack.to_int();
}

namespace {

std::uint64_t id(const typing::ConstructedType& t) {
  return t.name()->stamp()->id();
}

void load_value_tag_map(std::map<std::uint64_t, value_tag>& m) {
  const auto* b = ctx().builtin_types;
  m[id(*b->bool_type())] = value_tag::BOOL;
  m[id(*b->byte_type())] = value_tag::BYTE;
  m[id(*b->int_type())] = value_tag::INT;
  m[id(*b->bigint_type())] = value_tag::BIGINT;
  m[id(*b->float_type())] = value_tag::FLOAT;
  m[id(*b->char_type())] = value_tag::CHAR;
  m[id(*b->string_type())] = value_tag::STRING;
}

class TagVisitor : public typing::TypeVisitor {
 public:
  value_tag tag;

  void visit(const typing::TypeWithAgeRestriction& t) override {
    t.type()->accept(*this);
  }

  void visit(const typing::TypeVar&) override {
    throw std::logic_error("shouldn't have a typevar here");
  }

  void visit(const typing::UndeterminedType&) override {
    throw std::logic_error("shouldn't have an undetermined type here");
  }

  void visit(const typing::TupleType&) override { tag = value_tag::TUPLE; }

  void visit(const typing::RecordType&) override { tag = value_tag::TUPLE; }

  void visit(const typing::FunctionType&) override {
    tag = value_tag::FUNCTION;
  }

  void visit(const typing::ConstructedType& t) override {
    // Can't initialize statically because ctx().builtin_types isn't available.
    if (type_tags_.empty()) load_value_tag_map(type_tags_);

    auto it = type_tags_.find(id(t));
    if (it == end(type_tags_)) {
      tag = value_tag::CONSTRUCTED;
    } else {
      tag = it->second;
    }
  }

 private:
  static std::map<std::uint64_t, value_tag> type_tags_;
};

std::map<std::uint64_t, value_tag> TagVisitor::type_tags_;

void visit(const value_t& value, value_tag tag, const ManagedVisitor& visitor) {
  switch (tag) {
    case value_tag::BOOL:
    case value_tag::BYTE:
    case value_tag::INT:
    case value_tag::FLOAT:
    case value_tag::CHAR:
      break;

    case value_tag::BIGINT:
      value.bi().accept(visitor);
      break;

    case value_tag::STRING:
      value.str().accept(visitor);
      break;

    case value_tag::TUPLE:
      value.tup().accept(visitor);
      break;

    case value_tag::CONSTRUCTED:
      value.con().accept(visitor);
      break;

    case value_tag::FUNCTION:
      value.fun().accept(visitor);
      break;

    case value_tag::EXCEPTION_PACK:
      value.pack().accept(visitor);
      break;
  }
}

}  // namespace

value_tag compute_tag(typing::TypePtr type) {
  TagVisitor v;
  type->accept(v);
  return v.tag;
}

ManagedValue::ManagedValue(value_t value, value_tag tag)
    : value_(value), tag_(tag) {}

ManagedValue::~ManagedValue() = default;

value_t& ManagedValue::get() { return value_; }

const value_t& ManagedValue::get() const { return value_; }

void ManagedValue::visit_subobjects(const ManagedVisitor& visitor) {
  visit(value_, tag_, visitor);
}

ConstructedValue::ConstructedValue(std::size_t constructor)
    : constructor_(constructor) {}

ConstructedValue::ConstructedValue(std::size_t constructor, value_t arg,
                                   value_tag tag)
    : constructor_(constructor), arg_(arg), tag_(tag) {}

ConstructedValue::~ConstructedValue() = default;

std::size_t ConstructedValue::constructor() const { return constructor_; }

const std::optional<value_t>& ConstructedValue::arg() const { return arg_; }

void ConstructedValue::visit_subobjects(const ManagedVisitor& visitor) {
  if (arg_) visit(*arg_, tag_, visitor);
}

ExceptionPack::ExceptionPack(const Location& location,
                             std::u8string constructor)
    : location_(location), constructor_(std::move(constructor)) {}

ExceptionPack::ExceptionPack(const Location& location,
                             std::u8string constructor,
                             typing::TypePtr arg_type, value_t arg,
                             value_tag tag)
    : location_(location),
      constructor_(std::move(constructor)),
      arg_type_(arg_type),
      arg_(arg),
      tag_(tag) {}

ExceptionPack::~ExceptionPack() = default;

const Location& ExceptionPack::location() const { return location_; }

const std::u8string& ExceptionPack::constructor() const { return constructor_; }

typing::TypePtr ExceptionPack::arg_type() const { return arg_type_; }

const std::optional<value_t>& ExceptionPack::arg() const { return arg_; }

void ExceptionPack::visit_subobjects(const ManagedVisitor& visitor) {
  if (arg_) visit(*arg_, tag_, visitor);
}

FunctionValue::~FunctionValue() = default;

TupleValue::TupleValue(std::size_t count, value_tag tag)
    : buf_(ctx().mgr->allocate_private_buffer(count * sizeof(value_t))),
      tag_(tag) {
  for (std::size_t i = 0; i < count; ++i) {
    new (data() + i) value_t;
  }
}

TupleValue::~TupleValue() = default;

value_t& TupleValue::get(std::size_t i) { return *(data() + i); }

const value_t& TupleValue::get(std::size_t i) const { return *(data() + i); }

std::size_t TupleValue::size() const { return buf_.size() / sizeof(value_t); }

value_t* TupleValue::data() { return reinterpret_cast<value_t*>(buf_.buf()); }

const value_t* TupleValue::data() const {
  return reinterpret_cast<const value_t*>(buf_.buf());
}

void TupleValue::visit_subobjects(const ManagedVisitor& visitor) {
  for (std::size_t i = 0; i < size(); ++i) {
    visit(get(i), tag_, visitor);
  }
}

}  // namespace emil
