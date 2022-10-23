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

#include "emil/collections.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <functional>
#include <iterator>
#include <string>
#include <vector>

#include "emil/gc.h"

namespace emil::collections::testing {

class ManagedSetAccessor {
 public:
  template <ManagedType T, typename Comp>
  static void verify_invariants(const ManagedSet<T, Comp>& set) {
    detail::verify_invariants(set.tree_);
    ASSERT_EQ(std::distance(set.cbegin(), set.cend()), set.size_);
    for (auto it = set.cbegin();
         it != set.cend() && std::next(it) != set.cend(); ++it) {
      ASSERT_LT(**it, **std::next(it));
    }
  }
};

namespace {

using ::testing::ElementsAre;

class ManagedInt : public Managed {
 public:
  int n;

  explicit ManagedInt(int n) : n(n) {}

 private:
  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedInt);
  }

  void visit_subobjects(const ManagedVisitor&) override {}
};

[[maybe_unused]] bool operator<(const ManagedInt& l, const ManagedInt& r) {
  return l.n < r.n;
}

[[maybe_unused]] bool operator>(const ManagedInt& l, const ManagedInt& r) {
  return l.n > r.n;
}

[[maybe_unused]] bool operator==(const managed_ptr<ManagedInt>& l, int r) {
  return l->n == r;
}

managed_ptr<ManagedInt> mi(MemoryManager& mgr, int n) {
  return mgr.create<ManagedInt>(n);
}

TEST(ConsTest, Cons) {
  MemoryManager mgr;
  auto l = cons(mgr, mi(mgr, 1), nullptr);
  l = cons(mgr, mi(mgr, 2), std::move(l));
  l = cons(mgr, nullptr, std::move(l));
  ASSERT_FALSE(l->car);
  ASSERT_EQ(l->cdr->car, 2);
  ASSERT_EQ(l->cdr->cdr->car, 1);
  ASSERT_FALSE(l->cdr->cdr->cdr);
}

TEST(ManagedSetTest, OrderedAfterInserts) {
  MemoryManager mgr;
  auto s = mgr.create<ManagedSet<ManagedInt>>(mgr);
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 1)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 5)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 4)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 2)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 3)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 6)).first;
  ManagedSetAccessor::verify_invariants(*s);
  s = s->insert(mi(mgr, 7)).first;
  ManagedSetAccessor::verify_invariants(*s);
  std::vector<managed_ptr<ManagedInt>> v;
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, HandlesDuplicate) {
  MemoryManager mgr;
  auto s = mgr.create<ManagedSet<ManagedInt>>(mgr);
  ManagedSetAccessor::verify_invariants(*s);
  auto r = s->insert(mi(mgr, 1));
  EXPECT_TRUE(r.second);
  ManagedSetAccessor::verify_invariants(*r.first);
  s = r.first;

  r = s->insert(mi(mgr, 1));
  EXPECT_FALSE(r.second);
  ManagedSetAccessor::verify_invariants(*r.first);
  s = r.first;

  std::vector<managed_ptr<ManagedInt>> v;
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1));
}

TEST(ManagedSetTest, Factories) {
  MemoryManager mgr;
  auto s = managed_set(mgr, {mi(mgr, 1), mi(mgr, 3), mi(mgr, 2)});
  std::vector<managed_ptr<ManagedInt>> v;
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  EXPECT_THAT(v, ElementsAre(1, 2, 3));
  auto s2 =
      managed_set(mgr, std::greater<>(), {mi(mgr, 1), mi(mgr, 3), mi(mgr, 2)});
  v.clear();
  std::copy(s2->begin(), s2->end(), std::back_inserter(v));
  EXPECT_THAT(v, ElementsAre(3, 2, 1));
}

}  // namespace
}  // namespace emil::collections::testing
