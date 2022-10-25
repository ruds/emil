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
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

#include "emil/gc.h"
#include "testing/test_util.h"

namespace emil::collections::testing {

using TestRoot = emil::testing::TestRoot;

class ManagedSetAccessor {
 public:
  template <ManagedType T, typename Comp>
  static void verify_invariants(const ManagedSet<T, Comp>& set) {
    auto hold = set.mgr_->acquire_hold();
    detail::verify_invariants(set.tree_, *set.comp_);
    ASSERT_EQ(std::distance(set.cbegin(), set.cend()), set.size_);
    for (auto it = set.cbegin();
         it != set.cend() && std::next(it) != set.cend(); ++it) {
      ASSERT_LT(**it, **std::next(it));
    }
  }
};

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

[[maybe_unused]] std::ostream& operator<<(std::ostream& os,
                                          const ManagedInt& n) {
  return os << n.n;
}

[[maybe_unused]] std::ostream& operator<<(std::ostream& os,
                                          const managed_ptr<ManagedInt>& n) {
  return os << n->n;
}

[[maybe_unused]] bool operator<(const ManagedInt& l, const ManagedInt& r) {
  return l.n < r.n;
}

[[maybe_unused]] bool operator<(const ManagedInt& l, int r) { return l.n < r; }

[[maybe_unused]] bool operator<(int l, const ManagedInt& r) { return l < r.n; }

[[maybe_unused]] bool operator>(const ManagedInt& l, const ManagedInt& r) {
  return l.n > r.n;
}

struct managed_int_less {
  bool operator()(const ManagedInt& l, const auto& r) const { return l < r; }

  template <typename T>
  requires(!std::is_same_v<T, ManagedInt>) bool operator()(
      const T& l, const ManagedInt& r) const {
    return l < r;
  }
};

[[maybe_unused]] bool operator==(const managed_ptr<ManagedInt>& l, int r) {
  return l->n == r;
}

managed_ptr<ManagedInt> mi(MemoryManager& mgr, int n) {
  return mgr.create<ManagedInt>(n);
}

TEST(ConsTest, Cons) {
  TestRoot root;
  MemoryManager mgr(root);
  auto l = root.add_root(cons_in_place<ManagedInt>(mgr, nullptr, 1));
  auto i = root.add_root(mi(mgr, 2));
  l = root.replace_root(l, cons(mgr, i, l));
  root.remove_root(i);
  l = root.replace_root(l, cons_in_place(mgr, l, 3));
  l = root.replace_root(l, cons(mgr, nullptr, l));
  ASSERT_FALSE(l->car);
  ASSERT_EQ(l->cdr->car, 3);
  ASSERT_EQ(l->cdr->cdr->car, 2);
  ASSERT_EQ(l->cdr->cdr->cdr->car, 1);
  ASSERT_FALSE(l->cdr->cdr->cdr->cdr);
}

TEST(ManagedSetTest, OrderedAfterInserts) {
  TestRoot root;
  MemoryManager mgr(root);

  auto s = root.add_root(mgr.create<ManagedSet<ManagedInt, managed_int_less>>(
      mgr, managed_int_less{}));
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_FALSE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_FALSE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));

  s = root.replace_root(s, s->emplace(1).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_FALSE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_FALSE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(1), 1);

  s = root.replace_root(s, s->emplace(5).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_FALSE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_FALSE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(5), 5);

  s = root.replace_root(s, s->emplace(4).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_FALSE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(4), 4);

  s = root.replace_root(s, s->emplace(2).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);

  s = root.replace_root(s, s->emplace(3).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_FALSE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(3), 3);

  s = root.replace_root(s, s->emplace(6).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(6), 6);

  s = root.replace_root(s, s->emplace(7).first);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_TRUE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_TRUE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(7), 7);

  std::vector<managed_ptr<ManagedInt>> v;
  auto hold = mgr.acquire_hold();
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, HandlesDuplicate) {
  TestRoot root;
  MemoryManager mgr(root);
  auto s = root.add_root(mgr.create<ManagedSet<ManagedInt>>(mgr));
  ManagedSetAccessor::verify_invariants(*s);
  auto r = s->emplace(1);
  root.add_root(r.first);
  EXPECT_TRUE(r.second);
  ManagedSetAccessor::verify_invariants(*r.first);
  root.remove_root(s);
  s = r.first;

  r = s->emplace(1);
  EXPECT_FALSE(r.second);
  ASSERT_EQ(s, r.first);
  ManagedSetAccessor::verify_invariants(*s);

  std::vector<managed_ptr<ManagedInt>> v;
  auto hold = mgr.acquire_hold();
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1));
}

TEST(ManagedSetTest, Factories) {
  TestRoot root;
  MemoryManager mgr(root);
  auto hold = mgr.acquire_hold();

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

}  // namespace emil::collections::testing
