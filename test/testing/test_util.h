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
#include <functional>
#include <stdexcept>
#include <vector>

#include "emil/gc.h"

namespace emil::testing {

class TestRoot : public Root {
 public:
  template <ManagedType T>
  managed_ptr<T> add_root(managed_ptr<T> t) {
    roots_.push_back(t);
    return t;
  }

  template <ManagedType T>
  managed_ptr<T> replace_root(const managed_ptr<T>& old_root,
                              managed_ptr<T> t) {
    remove_root(old_root);
    roots_.push_back(t);
    return t;
  }

  template <ManagedType T>
  void remove_root(const managed_ptr<T>& old_root) {
    auto num = erase(roots_, old_root);
    if (num == 0) throw std::logic_error("Nothing to remove.");
  }

  void visit_root(const ManagedVisitor& visitor) override {
    std::for_each(roots_.begin(), roots_.end(),
                  std::bind(&managed_ptr_base::accept, std::placeholders::_1,
                            std::cref(visitor)));
  }

 private:
  std::vector<managed_ptr_base> roots_;
};

}  // namespace emil::testing
