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

#include <new>
#include <utility>

#include "emil/gc.h"
#include "emil/runtime.h"

namespace emil {

value_t::value_t() : b(false) {}
value_t::value_t(const value_t&) noexcept = default;
value_t& value_t::operator=(const value_t&) noexcept = default;
value_t::value_t(value_t&&) noexcept = default;
value_t& value_t::operator=(value_t&&) noexcept = default;
value_t::~value_t() = default;

namespace {

void visit(const value_t& value, value_tag tag, const ManagedVisitor& visitor) {
  switch (tag) {
    case value_tag::BOOL:
    case value_tag::BYTE:
    case value_tag::INT:
    case value_tag::FLOAT:
    case value_tag::CHAR:
      break;

    case value_tag::BIGINT:
      value.bi.accept(visitor);
      break;

    case value_tag::STRING:
      value.str.accept(visitor);
      break;

    case value_tag::TUPLE:
      value.tup.accept(visitor);
      break;

    case value_tag::CONSTRUCTED:
      value.con.accept(visitor);
      break;

    case value_tag::FUNCTION:
      value.fun.accept(visitor);
      break;

    case value_tag::EXCEPTION_PACK:
      value.pack.accept(visitor);
      break;
  }
}

}  // namespace

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
