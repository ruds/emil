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

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <new>
#include <optional>
#include <stdexcept>
#include <tuple>
#include <utility>

#include "emil/gc.h"
#include "emil/runtime.h"

namespace emil::collections {

/** A good old-fashioned LISPy list, with a car and a cons and
 * everything. */
template <ManagedType T>
struct ManagedCons : Managed {
  managed_ptr<T> car;
  managed_ptr<ManagedCons> cdr;

  ManagedCons(managed_ptr<T> car, managed_ptr<ManagedCons> cdr)
      : car(std::move(car)), cdr(std::move(cdr)) {}

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (car) car.accept(visitor);
    if (cdr) cdr.accept(visitor);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedCons);
  }
};

template <ManagedType T>
using ConsPtr = managed_ptr<ManagedCons<T>>;

/**
 * Prepend `car` to `cdr`.
 *
 * It is not safe to pass an unreachable `car` or `cdr` to this function and its
 * return value must be made reachable before any other allocations are made.
 */
template <ManagedType T>
ConsPtr<T> cons(managed_ptr<T> car, ConsPtr<T> cdr) {
  return make_managed<ManagedCons<T>>(std::move(car), std::move(cdr));
}

/** @overload */
template <ManagedType T>
ConsPtr<T> cons(managed_ptr<T> car, std::nullptr_t) {
  return make_managed<ManagedCons<T>>(std::move(car), nullptr);
}

/** @overload */
template <ManagedType T>
ConsPtr<T> cons(std::nullptr_t, ConsPtr<T> cdr) {
  return make_managed<ManagedCons<T>>(nullptr, std::move(cdr));
}

template <ManagedType T>
std::size_t len(ConsPtr<T> list) {
  std::size_t l = 0;
  while (list) {
    ++l;
    list = list->cdr;
  }
  return l;
}

/**
 * Construct and prepend a `T` to `cdr`.
 */
template <ManagedType T, typename... Args>
ConsPtr<T> cons_in_place(ConsPtr<T> cdr, Args&&... args) {
  auto hold = ctx().mgr->acquire_hold();
  // cppcheck-suppress redundantInitialization
  auto car = make_managed<T>(std::forward<Args>(args)...);
  return make_managed<ManagedCons<T>>(std::move(car), std::move(cdr));
}

}  // namespace emil::collections
