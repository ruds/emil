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

#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <variant>

#include "emil/bigint.h"  // IWYU pragma: keep
#include "emil/gc.h"
#include "emil/string.h"
#include "emil/token.h"
#include "emil/types.h"

namespace emil {

class ConstructedValue;
class ExceptionPack;
class FunctionValue;
class TupleValue;

union value_t {
  bool b;
  std::uint8_t byte;
  std::int64_t i;
  managed_ptr<bigint> bi;
  double fl;
  char32_t c;
  StringPtr str;
  managed_ptr<TupleValue> tup;
  managed_ptr<ConstructedValue> con;
  managed_ptr<FunctionValue> fun;
  managed_ptr<ExceptionPack> pack;

  value_t();
  value_t(const value_t&) noexcept;
  value_t& operator=(const value_t&) noexcept;
  value_t(value_t&&) noexcept;
  value_t& operator=(value_t&&) noexcept;
  ~value_t();
};

static_assert(sizeof(value_t) == sizeof(void*));

enum class value_tag {
  BOOL,
  BYTE,
  INT,
  BIGINT,
  FLOAT,
  CHAR,
  STRING,
  TUPLE,
  CONSTRUCTED,
  FUNCTION,
  EXCEPTION_PACK,
};

value_tag compute_tag(typing::TypePtr type);

using result_t = std::variant<value_t, managed_ptr<ExceptionPack>>;

class ManagedValue : public Managed {
 public:
  ManagedValue(value_t value, value_tag tag);
  ~ManagedValue() override;

  value_t& get();
  const value_t& get() const;

 private:
  value_t value_;
  value_tag tag_;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedValue);
  }
};

class ConstructedValue : public Managed {
 public:
  explicit ConstructedValue(std::size_t constructor);
  ConstructedValue(std::size_t constructor, value_t arg, value_tag tag);

  ~ConstructedValue() override;

  std::size_t constructor() const;
  const std::optional<value_t>& arg() const;

 private:
  std::size_t constructor_;
  std::optional<value_t> arg_;
  value_tag tag_;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ConstructedValue);
  }
};

class ExceptionPack : public Managed {
 public:
  explicit ExceptionPack(const Location& location, std::u8string constructor);
  ExceptionPack(const Location& location, std::u8string constructor,
                typing::TypePtr arg_type, value_t arg, value_tag tag);
  ~ExceptionPack() override;

  const Location& location() const;
  const std::u8string& constructor() const;
  typing::TypePtr arg_type() const;
  const std::optional<value_t>& arg() const;

 private:
  Location location_;
  std::u8string constructor_;
  typing::TypePtr arg_type_;
  std::optional<value_t> arg_;
  value_tag tag_;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(ExceptionPack);
  }
};

class FunctionValue : public Managed {
 public:
  ~FunctionValue() override;

  virtual result_t apply(value_t arg, typing::TypePtr type) const = 0;
};

class TupleValue : public Managed {
 public:
  TupleValue(std::size_t count, value_tag tag);
  ~TupleValue() override;

  value_t& get(std::size_t i);
  const value_t& get(std::size_t i) const;

  std::size_t size() const;

 private:
  PrivateBuffer buf_;
  value_tag tag_;

  value_t* data();
  const value_t* data() const;

  void visit_subobjects(const ManagedVisitor& visitor) override;
  std::size_t managed_size() const noexcept override {
    return sizeof(TupleValue);
  }
};

}  // namespace emil
