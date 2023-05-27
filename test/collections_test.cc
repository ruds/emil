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
#include <optional>
#include <random>
#include <stdexcept>
#include <utility>
#include <vector>

#include "emil/gc.h"
#include "emil/runtime.h"
#include "testing/test_util.h"

namespace emil::collections::testing {

using TestContext = emil::testing::TestContext;
using ::testing::AnyOf;
using ::testing::BeginEndDistanceIs;
using ::testing::ElementsAre;
using ::testing::Eq;

class ManagedSetAccessor {
 public:
  template <ManagedType T, typename Comp>
  static void verify_invariants(const ManagedSet<T, Comp>& set) {
    auto hold = ctx().mgr->acquire_hold();
    trees::verify_invariants(set.tree_, *set.comp_);
    ASSERT_EQ(std::distance(set.cbegin(), set.cend()), set.size_);
    for (auto it = set.cbegin();
         it != set.cend() && std::next(it) != set.cend(); ++it) {
      ASSERT_TRUE((*set.comp_)(**it, **std::next(it)));
    }
  }
};

class ManagedMapAccessor {
 public:
  template <ManagedType K, ManagedType V, typename Comp>
  static void verify_invariants(const ManagedMap<K, V, Comp>& map) {
    auto hold = ctx().mgr->acquire_hold();
    trees::verify_invariants(map.tree_, *map.comp_);
    ASSERT_EQ(std::distance(map.cbegin(), map.cend()), map.size_);
    for (auto it = map.cbegin();
         it != map.cend() && std::next(it) != map.cend(); ++it) {
      ASSERT_TRUE((*map.comp_)(*it->first, *std::next(it)->first));
    }
  }
};

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

[[maybe_unused]] bool operator==(const managed_ptr<ManagedInt>& l, int r) {
  return l->n == r;
}

managed_ptr<ManagedInt> mi(int n) { return make_managed<ManagedInt>(n); }

class ManagedDouble : public Managed {
 public:
  double d;

  explicit ManagedDouble(double d) : d(d) {}

 private:
  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedDouble);
  }

  void visit_subobjects(const ManagedVisitor&) override {}
};

[[maybe_unused]] std::ostream& operator<<(std::ostream& os,
                                          const ManagedDouble& d) {
  return os << d.d;
}

[[maybe_unused]] std::ostream& operator<<(std::ostream& os,
                                          const managed_ptr<ManagedDouble>& d) {
  return os << d->d;
}

[[maybe_unused]] bool operator==(const managed_ptr<ManagedDouble>& l,
                                 double r) {
  return l->d == r;
}

managed_ptr<ManagedDouble> md(double d) {
  return make_managed<ManagedDouble>(d);
}

[[maybe_unused]] bool operator==(
    const std::pair<managed_ptr<ManagedInt>, managed_ptr<ManagedDouble>>& l,
    const std::pair<int, double>& r) {
  return l.first == r.first && l.second == r.second;
}

[[maybe_unused]] bool operator==(
    const std::pair<managed_ptr<ManagedInt>, managed_ptr<ManagedInt>>& l,
    const std::pair<int, int>& r) {
  return l.first == r.first && l.second == r.second;
}

TEST(ManagedConsTest, Cons) {
  TestContext tc;
  auto l = tc.root.add_root(cons_in_place<ManagedInt>(nullptr, 1));
  EXPECT_EQ(len(l), 1);
  auto i = tc.root.add_root(mi(2));
  l = tc.root.replace_root(l, cons(i, l));
  EXPECT_EQ(len(l), 2);
  tc.root.remove_root(i);
  l = tc.root.replace_root(l, cons_in_place(l, 3));
  EXPECT_EQ(len(l), 3);
  l = tc.root.replace_root(l, cons(nullptr, l));
  [[maybe_unused]] auto force_gc = mi(4);
  EXPECT_EQ(len(l), 4);
  ASSERT_FALSE(l->car);
  ASSERT_EQ(l->cdr->car, 3);
  ASSERT_EQ(l->cdr->cdr->car, 2);
  ASSERT_EQ(l->cdr->cdr->cdr->car, 1);
  ASSERT_FALSE(l->cdr->cdr->cdr->cdr);
}

TEST(ManagedArrayTest, Empty) {
  TestContext tc;
  auto arr = tc.root.add_root(make_managed<ManagedArray<ManagedInt>>());
  EXPECT_TRUE(arr->empty());
  EXPECT_EQ(arr->size(), 0);
  EXPECT_THROW(arr->at(0), std::out_of_range);
  EXPECT_THAT(*arr, ElementsAre());
}

TEST(ManagedArrayTest, FromInitializerList) {
  TestContext tc;
  auto i1 = tc.root.add_root(mi(1));
  auto i2 = tc.root.add_root(mi(2));
  auto i3 = tc.root.add_root(mi(3));

  auto arr = tc.root.add_root(make_array({i1, i2, i3}));
  auto force_gc = mi(4);
  EXPECT_FALSE(arr->empty());
  EXPECT_EQ(arr->size(), 3);
  EXPECT_EQ((*arr)[0], 1);
  EXPECT_EQ((*arr)[1], 2);
  EXPECT_EQ((*arr)[2], 3);
  EXPECT_EQ(arr->at(0), 1);
  EXPECT_EQ(arr->at(1), 2);
  EXPECT_EQ(arr->at(2), 3);
  EXPECT_THROW(arr->at(3), std::out_of_range);
  EXPECT_THAT(*arr, ElementsAre(1, 2, 3));
}

TEST(ManagedArrayTest, FromTuples) {
  TestContext tc;
  auto arr = tc.root.add_root(make_array<ManagedInt>(
      std::make_tuple(1), std::make_tuple(2), std::make_tuple(3)));
  auto force_gc = mi(4);
  EXPECT_FALSE(arr->empty());
  EXPECT_EQ(arr->size(), 3);
  EXPECT_EQ((*arr)[0], 1);
  EXPECT_EQ((*arr)[1], 2);
  EXPECT_EQ((*arr)[2], 3);
  EXPECT_EQ(arr->at(0), 1);
  EXPECT_EQ(arr->at(1), 2);
  EXPECT_EQ(arr->at(2), 3);
  EXPECT_THROW(arr->at(3), std::out_of_range);
  EXPECT_THAT(*arr, ElementsAre(1, 2, 3));
}

TEST(ManagedArrayTest, FromList) {
  TestContext tc;
  auto list = tc.root.add_root(cons_in_place<ManagedInt>(nullptr, 3));
  list = tc.root.replace_root(list, cons_in_place(list, 2));
  list = tc.root.replace_root(list, cons_in_place(list, 1));
  EXPECT_EQ(len(list), 3);

  auto arr = tc.root.add_root(to_array(list));
  auto force_gc = mi(4);
  EXPECT_FALSE(arr->empty());
  EXPECT_EQ(arr->size(), 3);
  EXPECT_EQ((*arr)[0], 1);
  EXPECT_EQ((*arr)[1], 2);
  EXPECT_EQ((*arr)[2], 3);
  EXPECT_EQ(arr->at(0), 1);
  EXPECT_EQ(arr->at(1), 2);
  EXPECT_EQ(arr->at(2), 3);
  EXPECT_THROW(arr->at(3), std::out_of_range);
  EXPECT_THAT(*arr, ElementsAre(1, 2, 3));

  auto rarr = tc.root.add_root(to_array(list, true));
  force_gc = mi(4);
  EXPECT_FALSE(rarr->empty());
  EXPECT_EQ(rarr->size(), 3);
  EXPECT_EQ((*rarr)[0], 3);
  EXPECT_EQ((*rarr)[1], 2);
  EXPECT_EQ((*rarr)[2], 1);
  EXPECT_EQ(rarr->at(0), 3);
  EXPECT_EQ(rarr->at(1), 2);
  EXPECT_EQ(rarr->at(2), 1);
  EXPECT_THROW(rarr->at(3), std::out_of_range);
  EXPECT_THAT(*rarr, ElementsAre(3, 2, 1));
}

TEST(ManagedSetTest, OrderedAfterInserts) {
  TestContext tc;

  auto s = tc.root.add_root(make_managed<ManagedSet<ManagedInt>>());
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre());
  }

  s = tc.root.replace_root(s, s->emplace(1).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1));
  }

  s = tc.root.replace_root(s, s->emplace(5).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 5));
  }

  s = tc.root.replace_root(s, s->emplace(4).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 4, 5));
  }

  auto s145 = s;

  s = tc.root.add_root(s->emplace(2).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 4, 5));
    ASSERT_THAT(*s145, ElementsAre(1, 4, 5)) << "ManagedSet is not persistent.";
  }

  s = tc.root.replace_root(s, s->emplace(3).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5));
  }

  s = tc.root.replace_root(s, s->emplace(6).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6));
  }

  s = tc.root.replace_root(s, s->emplace(7).first);
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
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  std::vector<managed_ptr<ManagedInt>> v;
  auto hold = tc.mgr.acquire_hold();
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, HandlesDuplicate) {
  TestContext tc;
  auto s = tc.root.add_root(make_managed<ManagedSet<ManagedInt>>());
  ManagedSetAccessor::verify_invariants(*s);
  auto r = s->emplace(1);
  tc.root.add_root(r.first);
  EXPECT_TRUE(r.second);
  ManagedSetAccessor::verify_invariants(*r.first);
  tc.root.remove_root(s);
  s = r.first;

  r = s->emplace(1);
  EXPECT_FALSE(r.second);
  ASSERT_EQ(s, r.first);
  ManagedSetAccessor::verify_invariants(*s);

  std::vector<managed_ptr<ManagedInt>> v;
  auto hold = tc.mgr.acquire_hold();
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1));
}

TEST(ManagedSetTest, Factories) {
  TestContext tc;
  auto hold = tc.mgr.acquire_hold();

  auto s = managed_set({mi(1), mi(3), mi(2)});
  ManagedSetAccessor::verify_invariants(*s);
  EXPECT_THAT(*s, ElementsAre(1, 2, 3));

  auto s2 = managed_set(std::greater<>(), {mi(1), mi(3), mi(2)});
  ManagedSetAccessor::verify_invariants(*s2);
  EXPECT_THAT(*s2, ElementsAre(3, 2, 1));
}

TEST(ManagedSetTest, OrderedAfterDeletions) {
  TestContext tc;

  managed_ptr<ManagedSet<ManagedInt>> full_set;
  {
    auto hold = tc.mgr.acquire_hold();
    full_set = tc.root.add_root(
        managed_set({mi(1), mi(2), mi(3), mi(4), mi(5), mi(6), mi(7)}));
    ManagedSetAccessor::verify_invariants(*full_set);
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  auto result = full_set->erase(0);
  auto s = result.first;
  ASSERT_FALSE(result.second);
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
  ASSERT_EQ(*s->find(1), 1);
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(3), 3);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(5), 5);
  ASSERT_EQ(*s->find(6), 6);
  ASSERT_EQ(*s->find(7), 7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = full_set->erase(1);
  s = tc.root.add_root(result.first);
  ASSERT_TRUE(result.second);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_TRUE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_TRUE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(3), 3);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(5), 5);
  ASSERT_EQ(*s->find(6), 6);
  ASSERT_EQ(*s->find(7), 7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 5, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(5);
  s = tc.root.replace_root(s, result.first);
  ASSERT_TRUE(result.second);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_TRUE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(3), 3);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(6), 6);
  ASSERT_EQ(*s->find(7), 7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(7);
  s = tc.root.replace_root(s, result.first);
  ASSERT_TRUE(result.second);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_TRUE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(3), 3);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(6), 6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(3);
  s = tc.root.replace_root(s, result.first);
  ASSERT_TRUE(result.second);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(6), 6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(3);
  s = tc.root.replace_root(s, result.first);
  ASSERT_FALSE(result.second);
  ManagedSetAccessor::verify_invariants(*s);
  ASSERT_FALSE(s->contains(0));
  ASSERT_FALSE(s->contains(1));
  ASSERT_TRUE(s->contains(2));
  ASSERT_FALSE(s->contains(3));
  ASSERT_TRUE(s->contains(4));
  ASSERT_FALSE(s->contains(5));
  ASSERT_TRUE(s->contains(6));
  ASSERT_FALSE(s->contains(7));
  ASSERT_FALSE(s->contains(8));
  ASSERT_EQ(*s->find(2), 2);
  ASSERT_EQ(*s->find(4), 4);
  ASSERT_EQ(*s->find(6), 6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  auto empty_set = tc.root.add_root(managed_set<ManagedInt>({}));
  result = empty_set->erase(3);
  ASSERT_FALSE(result.second);
  ASSERT_EQ(result.first, empty_set);
  ManagedSetAccessor::verify_invariants(*empty_set);
  auto hold = tc.mgr.acquire_hold();
  ASSERT_THAT(*empty_set, ElementsAre());
  ASSERT_THAT(*s, ElementsAre(2, 4, 6));
  ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, Union) {
  TestContext tc;
  managed_ptr<ManagedSet<ManagedInt>> empty;
  managed_ptr<ManagedSet<ManagedInt>> s234;
  managed_ptr<ManagedSet<ManagedInt>> s56;
  managed_ptr<ManagedSet<ManagedInt>> s135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_set<ManagedInt>();
    s234 = managed_set({mi(2), mi(3), mi(4)});
    s56 = managed_set({mi(5), mi(6)});
    s135 = managed_set({mi(1), mi(3), mi(5)});
    tc.root.add_root(empty);
    tc.root.add_root(s234);
    tc.root.add_root(s56);
    tc.root.add_root(s135);
  }
  auto empty_or_empty = tc.root.add_root(empty | empty);
  auto empty_or_s234 = tc.root.add_root(empty | s234);
  auto s234_or_empty = tc.root.add_root(s234 | empty);

  auto s234_or_s234 = tc.root.add_root(s234 | s234);
  auto s234_or_s56 = tc.root.add_root(s234 | s56);
  auto s56_or_s234 = tc.root.add_root(s56 | s234);
  auto s234_or_s135 = tc.root.add_root(s234 | s135);
  auto s135_or_s234 = tc.root.add_root(s135 | s234);

  auto s56_or_s135 = tc.root.add_root(s56 | s135);
  auto s135_or_s56 = tc.root.add_root(s135 | s56);

  auto all_a = tc.root.add_root(s234_or_s56 | s135);
  auto all_b = tc.root.add_root(s135 | s234_or_s56);
  auto all_c = tc.root.add_root(s56 | s135_or_s234);
  auto all_d = tc.root.add_root(s135_or_s234 | s56);
  auto all_e = tc.root.add_root(all_a | all_d);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_or_empty, ElementsAre());
  EXPECT_THAT(*empty_or_s234, ElementsAre(2, 3, 4));
  EXPECT_THAT(*s234_or_empty, ElementsAre(2, 3, 4));

  EXPECT_THAT(*s234_or_s234, ElementsAre(2, 3, 4));
  EXPECT_THAT(*s234_or_s56, ElementsAre(2, 3, 4, 5, 6));
  EXPECT_THAT(*s56_or_s234, ElementsAre(2, 3, 4, 5, 6));
  EXPECT_THAT(*s234_or_s135, ElementsAre(1, 2, 3, 4, 5));
  EXPECT_THAT(*s135_or_s234, ElementsAre(1, 2, 3, 4, 5));

  EXPECT_THAT(*s56_or_s135, ElementsAre(1, 3, 5, 6));
  EXPECT_THAT(*s135_or_s56, ElementsAre(1, 3, 5, 6));

  EXPECT_THAT(*all_a, ElementsAre(1, 2, 3, 4, 5, 6));
  EXPECT_THAT(*all_b, ElementsAre(1, 2, 3, 4, 5, 6));
  EXPECT_THAT(*all_c, ElementsAre(1, 2, 3, 4, 5, 6));
  EXPECT_THAT(*all_d, ElementsAre(1, 2, 3, 4, 5, 6));
  EXPECT_THAT(*all_e, ElementsAre(1, 2, 3, 4, 5, 6));
}

TEST(ManagedSetTest, Intersection) {
  TestContext tc;
  managed_ptr<ManagedSet<ManagedInt>> empty;
  managed_ptr<ManagedSet<ManagedInt>> all;
  managed_ptr<ManagedSet<ManagedInt>> s234;
  managed_ptr<ManagedSet<ManagedInt>> s56;
  managed_ptr<ManagedSet<ManagedInt>> s135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_set<ManagedInt>();
    all = managed_set({mi(1), mi(2), mi(3), mi(4), mi(5), mi(6), mi(7)});
    s234 = managed_set({mi(2), mi(3), mi(4)});
    s56 = managed_set({mi(5), mi(6)});
    s135 = managed_set({mi(1), mi(3), mi(5)});
    tc.root.add_root(empty);
    tc.root.add_root(all);
    tc.root.add_root(s234);
    tc.root.add_root(s56);
    tc.root.add_root(s135);
  }
  auto empty_and_empty = tc.root.add_root(empty & empty);
  auto empty_and_s234 = tc.root.add_root(empty & s234);
  auto s234_and_empty = tc.root.add_root(s234 & empty);

  auto s234_and_s234 = tc.root.add_root(s234 & s234);
  auto s234_and_s56 = tc.root.add_root(s234 & s56);
  auto s56_and_s234 = tc.root.add_root(s56 & s234);
  auto s234_and_s135 = tc.root.add_root(s234 & s135);
  auto s135_and_s234 = tc.root.add_root(s135 & s234);
  auto s234_and_all = tc.root.add_root(s234 & all);
  auto all_and_s234 = tc.root.add_root(all & s234);

  auto s56_and_s135 = tc.root.add_root(s56 & s135);
  auto s135_and_s56 = tc.root.add_root(s135 & s56);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_and_empty, ElementsAre());
  EXPECT_THAT(*empty_and_s234, ElementsAre());
  EXPECT_THAT(*s234_and_empty, ElementsAre());

  EXPECT_THAT(*s234_and_s234, ElementsAre(2, 3, 4));
  EXPECT_THAT(*s234_and_s56, ElementsAre());
  EXPECT_THAT(*s56_and_s234, ElementsAre());
  EXPECT_THAT(*s234_and_s135, ElementsAre(3));
  EXPECT_THAT(*s135_and_s234, ElementsAre(3));
  EXPECT_THAT(*s234_and_all, ElementsAre(2, 3, 4));
  EXPECT_THAT(*all_and_s234, ElementsAre(2, 3, 4));

  EXPECT_THAT(*s56_and_s135, ElementsAre(5));
  EXPECT_THAT(*s135_and_s56, ElementsAre(5));
}

TEST(ManagedSetTest, Difference) {
  TestContext tc;
  managed_ptr<ManagedSet<ManagedInt>> empty;
  managed_ptr<ManagedSet<ManagedInt>> all;
  managed_ptr<ManagedSet<ManagedInt>> s234;
  managed_ptr<ManagedSet<ManagedInt>> s56;
  managed_ptr<ManagedSet<ManagedInt>> s135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_set<ManagedInt>();
    all = managed_set({mi(1), mi(2), mi(3), mi(4), mi(5), mi(6)});
    s234 = managed_set({mi(2), mi(3), mi(4)});
    s56 = managed_set({mi(5), mi(6)});
    s135 = managed_set({mi(1), mi(3), mi(5)});
    tc.root.add_root(empty);
    tc.root.add_root(all);
    tc.root.add_root(s234);
    tc.root.add_root(s56);
    tc.root.add_root(s135);
  }
  auto empty_minus_empty = tc.root.add_root(empty - empty);
  auto empty_minus_s234 = tc.root.add_root(empty - s234);
  auto s234_minus_empty = tc.root.add_root(s234 - empty);

  auto s234_minus_s234 = tc.root.add_root(s234 - s234);
  auto s234_minus_s56 = tc.root.add_root(s234 - s56);
  auto s56_minus_s234 = tc.root.add_root(s56 - s234);
  auto s234_minus_s135 = tc.root.add_root(s234 - s135);
  auto s135_minus_s234 = tc.root.add_root(s135 - s234);
  auto s234_minus_all = tc.root.add_root(s234 - all);
  auto all_minus_s234 = tc.root.add_root(all - s234);

  auto s56_minus_s135 = tc.root.add_root(s56 - s135);
  auto s135_minus_s56 = tc.root.add_root(s135 - s56);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_minus_empty, ElementsAre());
  EXPECT_THAT(*empty_minus_s234, ElementsAre());
  EXPECT_THAT(*s234_minus_empty, ElementsAre(2, 3, 4));

  EXPECT_THAT(*s234_minus_s234, ElementsAre());
  EXPECT_THAT(*s234_minus_s56, ElementsAre(2, 3, 4));
  EXPECT_THAT(*s56_minus_s234, ElementsAre(5, 6));
  EXPECT_THAT(*s234_minus_s135, ElementsAre(2, 4));
  EXPECT_THAT(*s135_minus_s234, ElementsAre(1, 5));
  EXPECT_THAT(*s234_minus_all, ElementsAre());
  EXPECT_THAT(*all_minus_s234, ElementsAre(1, 5, 6));

  EXPECT_THAT(*s56_minus_s135, ElementsAre(6));
  EXPECT_THAT(*s135_minus_s56, ElementsAre(1, 3));
}

TEST(ManagedSetTest, Stress) {
  std::random_device rand_dev;
  std::mt19937 generator(rand_dev());
  std::uniform_int_distribution<int> dist(-128, 127);

  TestContext tc;
  auto prev = tc.root.add_root(managed_set<ManagedInt>());
  for (int run = 0; run < 2; ++run) {
    auto s = tc.root.add_root(make_managed<ManagedSet<ManagedInt>>());
    std::size_t size = 0;
    for (int i = 0; i < 1000; ++i) {
      const int num = dist(generator);
      if (s->contains(num)) {
        ASSERT_EQ(*s->find(num), num);
        auto insert_result = s->emplace(num);
        ASSERT_FALSE(insert_result.second);
        ASSERT_EQ(insert_result.first, s);
        auto erase_result = s->erase(num);
        ASSERT_TRUE(erase_result.second);
        ASSERT_NE(erase_result.first, s);
        s = tc.root.replace_root(s, erase_result.first);
        ASSERT_FALSE(s->contains(num));
        --size;
      } else {
        auto erase_result = s->erase(num);
        ASSERT_FALSE(erase_result.second);
        ASSERT_EQ(erase_result.first, s);
        auto insert_result = s->emplace(num);
        ASSERT_TRUE(insert_result.second);
        ASSERT_NE(insert_result.first, s);
        s = tc.root.replace_root(s, insert_result.first);
        ASSERT_TRUE(s->contains(num));
        ASSERT_EQ(*s->find(num), num);
        ++size;
      }
      ASSERT_EQ(s->size(), size);
      {
        auto hold = tc.mgr.acquire_hold();
        ASSERT_THAT(*s, BeginEndDistanceIs(size));
      }
      ASSERT_EQ(s->empty(), size == 0);
      ManagedSetAccessor::verify_invariants(*s);
    }
    auto u1 = tc.root.add_root(prev | s);
    auto u2 = tc.root.add_root(s | prev);
    ManagedSetAccessor::verify_invariants(*u1);
    ManagedSetAccessor::verify_invariants(*u2);
    auto i1 = tc.root.add_root(prev & s);
    auto i2 = tc.root.add_root(s & prev);
    ManagedSetAccessor::verify_invariants(*i1);
    ManagedSetAccessor::verify_invariants(*i2);
    auto d1 = tc.root.add_root(prev - s);
    auto d2 = tc.root.add_root(s - prev);
    ManagedSetAccessor::verify_invariants(*d1);
    ManagedSetAccessor::verify_invariants(*d2);
    {
      auto hold = tc.mgr.acquire_hold();
      ASSERT_THAT(*u1, BeginEndDistanceIs(u1->size()));
      ASSERT_THAT(*u2, BeginEndDistanceIs(u2->size()));
      for (const auto& el : *s) {
        ASSERT_TRUE(u1->contains(*el));
        ASSERT_TRUE(u2->contains(*el));
      }
      for (const auto& el : *prev) {
        ASSERT_TRUE(u1->contains(*el));
        ASSERT_TRUE(u2->contains(*el));
      }
      for (const auto& el : *u1) {
        ASSERT_TRUE(s->contains(*el) || prev->contains(*el));
      }
      for (const auto& el : *u2) {
        ASSERT_TRUE(s->contains(*el) || prev->contains(*el));
      }

      ASSERT_THAT(*i1, BeginEndDistanceIs(i1->size()));
      ASSERT_THAT(*i2, BeginEndDistanceIs(i2->size()));
      for (const auto& el : *s) {
        if (prev->contains(*el)) {
          ASSERT_TRUE(i1->contains(*el));
          ASSERT_TRUE(i2->contains(*el));
        } else {
          ASSERT_FALSE(i1->contains(*el));
          ASSERT_FALSE(i2->contains(*el));
        }
      }
      for (const auto& el : *prev) {
        if (s->contains(*el)) {
          ASSERT_TRUE(i1->contains(*el));
          ASSERT_TRUE(i2->contains(*el));
        } else {
          ASSERT_FALSE(i1->contains(*el));
          ASSERT_FALSE(i2->contains(*el));
        }
      }
      for (const auto& el : *i1) {
        ASSERT_TRUE(s->contains(*el) && prev->contains(*el));
      }
      for (const auto& el : *i2) {
        ASSERT_TRUE(s->contains(*el) && prev->contains(*el));
      }

      ASSERT_THAT(*d1, BeginEndDistanceIs(d1->size()));
      ASSERT_THAT(*d2, BeginEndDistanceIs(d2->size()));
      for (const auto& el : *s) {
        if (prev->contains(*el)) {
          ASSERT_FALSE(d1->contains(*el));
          ASSERT_FALSE(d2->contains(*el));
        } else {
          ASSERT_FALSE(d1->contains(*el));
          ASSERT_TRUE(d2->contains(*el));
        }
      }
      for (const auto& el : *prev) {
        if (s->contains(*el)) {
          ASSERT_FALSE(d1->contains(*el));
          ASSERT_FALSE(d2->contains(*el));
        } else {
          ASSERT_TRUE(d1->contains(*el));
          ASSERT_FALSE(d2->contains(*el));
        }
      }
      for (const auto& el : *d1) {
        ASSERT_TRUE(!s->contains(*el) && prev->contains(*el));
      }
      for (const auto& el : *d2) {
        ASSERT_TRUE(s->contains(*el) && !prev->contains(*el));
      }
    }
    prev = s;
  }
}

std::pair<managed_ptr<ManagedMap<ManagedInt, ManagedDouble>>,
          std::optional<managed_ptr<ManagedDouble>>>
emplace(const ManagedMap<ManagedInt, ManagedDouble>& m, int i, double d) {
  return m.emplace(std::make_tuple(i), std::make_tuple(d));
}

#define MP(x, y) std::make_pair(x, y)

TEST(ManagedMapTest, OrderedAfterInserts) {
  TestContext tc;

  auto m =
      tc.root.add_root(make_managed<ManagedMap<ManagedInt, ManagedDouble>>());
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_FALSE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_FALSE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre());
  }

  m = tc.root.replace_root(m, emplace(*m, 1, -1.0).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_FALSE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_FALSE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(1), -1.0);
  ASSERT_EQ(*m->find(1), MP(1, -1.0));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0)));
  }

  m = tc.root.replace_root(m, emplace(*m, 5, -2.3).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_FALSE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_FALSE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(5), -2.3);
  ASSERT_EQ(*m->find(5), MP(5, -2.3));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(5, -2.3)));
  }

  m = tc.root.replace_root(m, emplace(*m, 4, 1e5).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_FALSE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(4), 1e5);
  ASSERT_EQ(*m->find(4), MP(4, 1e5));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(4, 1e5), MP(5, -2.3)));
  }

  auto m145 = m;

  m = tc.root.add_root(emplace(*m, 2, 4.25).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), 4.25);
  ASSERT_EQ(*m->find(2), MP(2, 4.25));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(4, 1e5), MP(5, -2.3)));
    ASSERT_THAT(*m145, ElementsAre(MP(1, -1.0), MP(4, 1e5), MP(5, -2.3)))
        << "ManagedMap is not persistent";
  }

  m = tc.root.replace_root(m, emplace(*m, 3, 1e-14).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_FALSE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(3), 1e-14);
  ASSERT_EQ(*m->find(3), MP(3, 1e-14));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14),
                                MP(4, 1e5), MP(5, -2.3)));
  }

  m = tc.root.replace_root(m, emplace(*m, 6, 3.14).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(6), 3.14);
  ASSERT_EQ(*m->find(6), MP(6, 3.14));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14),
                                MP(4, 1e5), MP(5, -2.3), MP(6, 3.14)));
  }

  m = tc.root.replace_root(m, emplace(*m, 7, 2.718).first);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_TRUE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(7), 2.718);
  ASSERT_EQ(*m->find(7), MP(7, 2.718));
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                            MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
  }

  std::vector<std::pair<managed_ptr<ManagedInt>, managed_ptr<ManagedDouble>>> v;
  auto hold = tc.mgr.acquire_hold();
  std::copy(m->begin(), m->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                             MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
  ASSERT_THAT(*m,
              ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                          MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
}

TEST(ManagedMapTest, HandlesRemapping) {
  TestContext tc;
  auto m =
      tc.root.add_root(make_managed<ManagedMap<ManagedInt, ManagedDouble>>());
  ManagedMapAccessor::verify_invariants(*m);
  EXPECT_FALSE(m->get(1));

  auto r = emplace(*m, 1, 1.0);
  EXPECT_NE(m, r.first);
  tc.root.add_root(r.first);
  EXPECT_FALSE(r.second);
  ManagedMapAccessor::verify_invariants(*m);
  ManagedMapAccessor::verify_invariants(*r.first);
  tc.root.remove_root(m);
  m = r.first;
  EXPECT_EQ(m->get(1), 1.0);
  EXPECT_EQ(*m->find(1), MP(1, 1.0));

  r = emplace(*m, 1, -1.0);
  EXPECT_NE(m, r.first);
  tc.root.add_root(r.first);
  EXPECT_EQ(r.second, 1);
  ManagedMapAccessor::verify_invariants(*m);
  ManagedMapAccessor::verify_invariants(*r.first);
  EXPECT_EQ(m->get(1), 1.0);
  EXPECT_EQ(*m->find(1), MP(1, 1.0));
  EXPECT_EQ(r.first->get(1), -1.0);
  EXPECT_EQ(*r.first->find(1), MP(1, -1.0));

  auto hold = tc.mgr.acquire_hold();
  ASSERT_THAT(*m, ElementsAre(MP(1, 1.0)));
  ASSERT_THAT(*r.first, ElementsAre(MP(1, -1.0)));
}

TEST(ManagedMapTest, Factories) {
  TestContext tc;
  auto hold = tc.mgr.acquire_hold();

  auto m =
      managed_map({MP(mi(1), md(1.0)), MP(mi(3), md(3.0)), MP(mi(2), md(2.0))});
  ManagedMapAccessor::verify_invariants(*m);
  EXPECT_THAT(*m, ElementsAre(MP(1, 1.0), MP(2, 2.0), MP(3, 3.0)));

  auto m2 =
      managed_map(std::greater<>(),
                  {MP(mi(1), md(1.0)), MP(mi(3), md(3.0)), MP(mi(2), md(2.0))});
  ManagedMapAccessor::verify_invariants(*m2);
  EXPECT_THAT(*m2, ElementsAre(MP(3, 3.0), MP(2, 2.0), MP(1, 1.0)));
}

TEST(ManagedMapTest, OrderedAfterDeletions) {
  TestContext tc;

  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> full_map;
  {
    auto hold = tc.mgr.acquire_hold();
    full_map = tc.root.add_root(managed_map({
        MP(mi(1), md(-1.0)),
        MP(mi(2), md(-2.0)),
        MP(mi(3), md(-3.0)),
        MP(mi(4), md(-4.0)),
        MP(mi(5), md(-5.0)),
        MP(mi(6), md(-6.0)),
        MP(mi(7), md(-7.0)),
    }));
    ManagedMapAccessor::verify_invariants(*full_map);
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  auto result = full_map->erase(0);
  auto m = result.first;
  ASSERT_FALSE(result.second);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_TRUE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_TRUE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(1), -1);
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(3), -3);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(5), -5);
  ASSERT_EQ(m->get(6), -6);
  ASSERT_EQ(m->get(7), -7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = full_map->erase(1);
  m = tc.root.add_root(result.first);
  ASSERT_EQ(result.second, -1.0);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_TRUE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_TRUE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(3), -3);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(5), -5);
  ASSERT_EQ(m->get(6), -6);
  ASSERT_EQ(m->get(7), -7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                                MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(5);
  m = tc.root.replace_root(m, result.first);
  ASSERT_EQ(result.second, -5.0);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_TRUE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(3), -3);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(6), -6);
  ASSERT_EQ(m->get(7), -7);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                                MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(7);
  m = tc.root.replace_root(m, result.first);
  ASSERT_EQ(result.second, -7.0);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_TRUE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(3), -3);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(6), -6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(
        *m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(3);
  m = tc.root.replace_root(m, result.first);
  ASSERT_EQ(result.second, -3.0);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(6), -6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(3);
  m = tc.root.replace_root(m, result.first);
  ASSERT_FALSE(result.second);
  ManagedMapAccessor::verify_invariants(*m);
  ASSERT_FALSE(m->contains(0));
  ASSERT_FALSE(m->contains(1));
  ASSERT_TRUE(m->contains(2));
  ASSERT_FALSE(m->contains(3));
  ASSERT_TRUE(m->contains(4));
  ASSERT_FALSE(m->contains(5));
  ASSERT_TRUE(m->contains(6));
  ASSERT_FALSE(m->contains(7));
  ASSERT_FALSE(m->contains(8));
  ASSERT_EQ(m->get(2), -2);
  ASSERT_EQ(m->get(4), -4);
  ASSERT_EQ(m->get(6), -6);
  {
    auto hold = tc.mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  auto empty_map = tc.root.add_root(managed_map<ManagedInt, ManagedDouble>({}));
  result = empty_map->erase(3);
  ASSERT_FALSE(result.second);
  ASSERT_EQ(result.first, empty_map);
  ManagedMapAccessor::verify_invariants(*empty_map);
  auto hold = tc.mgr.acquire_hold();
  ASSERT_THAT(*empty_map, ElementsAre());
  ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(4, -4.0), MP(6, -6.0)));
  ASSERT_THAT(*full_map,
              ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                          MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
}

TEST(ManagedMapTest, Union) {
  TestContext tc;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> empty;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m234;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m56;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_map<ManagedInt, ManagedDouble>();
    m234 = emplace(*empty, 2, 234).first;
    m234 = emplace(*m234, 3, 234).first;
    m234 = emplace(*m234, 4, 234).first;
    m56 = emplace(*empty, 5, 56).first;
    m56 = emplace(*m56, 6, 56).first;
    m135 = emplace(*empty, 1, 135).first;
    m135 = emplace(*m135, 3, 135).first;
    m135 = emplace(*m135, 5, 135).first;
    tc.root.add_root(empty);
    tc.root.add_root(m234);
    tc.root.add_root(m56);
    tc.root.add_root(m135);
  }
  auto empty_or_empty = tc.root.add_root(empty | empty);
  auto empty_or_m234 = tc.root.add_root(empty | m234);
  auto m234_or_empty = tc.root.add_root(m234 | empty);

  auto m234_or_m234 = tc.root.add_root(m234 | m234);
  auto m234_or_m56 = tc.root.add_root(m234 | m56);
  auto m56_or_m234 = tc.root.add_root(m56 | m234);
  auto m234_or_m135 = tc.root.add_root(m234 | m135);
  auto m135_or_m234 = tc.root.add_root(m135 | m234);

  auto m56_or_m135 = tc.root.add_root(m56 | m135);
  auto m135_or_m56 = tc.root.add_root(m135 | m56);

  auto all_a = tc.root.add_root(m234_or_m56 | m135);
  auto all_b = tc.root.add_root(m135 | m234_or_m56);
  auto all_c = tc.root.add_root(m56 | m135_or_m234);
  auto all_d = tc.root.add_root(m135_or_m234 | m56);
  auto all_e = tc.root.add_root(all_a | all_d);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_or_empty, ElementsAre());
  EXPECT_THAT(*empty_or_m234, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*m234_or_empty, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));

  EXPECT_THAT(*m234_or_m234, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*m234_or_m56, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234),
                                        MP(5, 56), MP(6, 56)));
  EXPECT_THAT(*m56_or_m234, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234),
                                        MP(5, 56), MP(6, 56)));
  EXPECT_THAT(*m234_or_m135, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 135),
                                         MP(4, 234), MP(5, 135)));
  EXPECT_THAT(*m135_or_m234, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 234),
                                         MP(4, 234), MP(5, 135)));

  EXPECT_THAT(*m56_or_m135,
              ElementsAre(MP(1, 135), MP(3, 135), MP(5, 135), MP(6, 56)));
  EXPECT_THAT(*m135_or_m56,
              ElementsAre(MP(1, 135), MP(3, 135), MP(5, 56), MP(6, 56)));

  EXPECT_THAT(*all_a, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 135),
                                  MP(4, 234), MP(5, 135), MP(6, 56)));
  EXPECT_THAT(*all_b, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 234),
                                  MP(4, 234), MP(5, 56), MP(6, 56)));
  EXPECT_THAT(*all_c, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 234),
                                  MP(4, 234), MP(5, 135), MP(6, 56)));
  EXPECT_THAT(*all_d, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 234),
                                  MP(4, 234), MP(5, 56), MP(6, 56)));
  EXPECT_THAT(*all_e, ElementsAre(MP(1, 135), MP(2, 234), MP(3, 234),
                                  MP(4, 234), MP(5, 56), MP(6, 56)));
}

TEST(ManagedMapTest, Intersection) {
  TestContext tc;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> empty;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> all;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m234;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m56;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_map<ManagedInt, ManagedDouble>();
    all = emplace(*empty, 1, 123456).first;
    all = emplace(*all, 2, 123456).first;
    all = emplace(*all, 3, 123456).first;
    all = emplace(*all, 4, 123456).first;
    all = emplace(*all, 5, 123456).first;
    all = emplace(*all, 6, 123456).first;
    m234 = emplace(*empty, 2, 234).first;
    m234 = emplace(*m234, 3, 234).first;
    m234 = emplace(*m234, 4, 234).first;
    m56 = emplace(*empty, 5, 56).first;
    m56 = emplace(*m56, 6, 56).first;
    m135 = emplace(*empty, 1, 135).first;
    m135 = emplace(*m135, 3, 135).first;
    m135 = emplace(*m135, 5, 135).first;
    tc.root.add_root(empty);
    tc.root.add_root(all);
    tc.root.add_root(m234);
    tc.root.add_root(m56);
    tc.root.add_root(m135);
  }
  auto empty_and_empty = tc.root.add_root(empty & empty);
  auto empty_and_m234 = tc.root.add_root(empty & m234);
  auto m234_and_empty = tc.root.add_root(m234 & empty);

  auto m234_and_m234 = tc.root.add_root(m234 & m234);
  auto m234_and_m56 = tc.root.add_root(m234 & m56);
  auto m56_and_m234 = tc.root.add_root(m56 & m234);
  auto m234_and_m135 = tc.root.add_root(m234 & m135);
  auto m135_and_m234 = tc.root.add_root(m135 & m234);
  auto m234_and_all = tc.root.add_root(m234 & all);
  auto all_and_m234 = tc.root.add_root(all & m234);

  auto m56_and_m135 = tc.root.add_root(m56 & m135);
  auto m135_and_m56 = tc.root.add_root(m135 & m56);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_and_empty, ElementsAre());
  EXPECT_THAT(*empty_and_m234, ElementsAre());
  EXPECT_THAT(*m234_and_empty, ElementsAre());

  EXPECT_THAT(*m234_and_m234, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*m234_and_m56, ElementsAre());
  EXPECT_THAT(*m56_and_m234, ElementsAre());
  EXPECT_THAT(*m234_and_m135, ElementsAre(MP(3, 135)));
  EXPECT_THAT(*m135_and_m234, ElementsAre(MP(3, 234)));
  EXPECT_THAT(*m234_and_all,
              ElementsAre(MP(2, 123456), MP(3, 123456), MP(4, 123456)));
  EXPECT_THAT(*all_and_m234, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));

  EXPECT_THAT(*m56_and_m135, ElementsAre(MP(5, 135)));
  EXPECT_THAT(*m135_and_m56, ElementsAre(MP(5, 56)));
}

TEST(ManagedMapTest, FilterKeys) {
  TestContext tc;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> empty;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> all;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m234;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m56;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m135;
  managed_ptr<ManagedSet<ManagedInt>> k_empty;
  managed_ptr<ManagedSet<ManagedInt>> k_all;
  managed_ptr<ManagedSet<ManagedInt>> k_m234;
  managed_ptr<ManagedSet<ManagedInt>> k_m56;
  managed_ptr<ManagedSet<ManagedInt>> k_m135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_map<ManagedInt, ManagedDouble>();
    k_empty = managed_set<ManagedInt>();
    all = emplace(*empty, 1, 123456).first;
    all = emplace(*all, 2, 123456).first;
    all = emplace(*all, 3, 123456).first;
    all = emplace(*all, 4, 123456).first;
    all = emplace(*all, 5, 123456).first;
    all = emplace(*all, 6, 123456).first;
    k_all = managed_set({mi(1), mi(2), mi(3), mi(4), mi(5), mi(6)});
    m234 = emplace(*empty, 2, 234).first;
    m234 = emplace(*m234, 3, 234).first;
    m234 = emplace(*m234, 4, 234).first;
    k_m234 = managed_set({mi(2), mi(3), mi(4)});
    m56 = emplace(*empty, 5, 56).first;
    m56 = emplace(*m56, 6, 56).first;
    k_m56 = managed_set({mi(5), mi(6)});
    m135 = emplace(*empty, 1, 135).first;
    m135 = emplace(*m135, 3, 135).first;
    m135 = emplace(*m135, 5, 135).first;
    k_m135 = managed_set({mi(1), mi(3), mi(5)});
    tc.root.add_root(empty);
    tc.root.add_root(all);
    tc.root.add_root(m234);
    tc.root.add_root(m56);
    tc.root.add_root(m135);
    tc.root.add_root(k_empty);
    tc.root.add_root(k_all);
    tc.root.add_root(k_m234);
    tc.root.add_root(k_m56);
    tc.root.add_root(k_m135);
  }
  auto empty_filtered_by_empty = tc.root.add_root(empty->filter_keys(k_empty));
  auto empty_filtered_by_m234 = tc.root.add_root(empty->filter_keys(k_m234));
  auto m234_filtered_by_empty = tc.root.add_root(m234->filter_keys(k_empty));

  auto m234_filtered_by_m234 = tc.root.add_root(m234->filter_keys(k_m234));
  auto m234_filtered_by_m56 = tc.root.add_root(m234->filter_keys(k_m56));
  auto m56_filtered_by_m234 = tc.root.add_root(m56->filter_keys(k_m234));
  auto m234_filtered_by_m135 = tc.root.add_root(m234->filter_keys(k_m135));
  auto m135_filtered_by_m234 = tc.root.add_root(m135->filter_keys(k_m234));
  auto m234_filtered_by_all = tc.root.add_root(m234->filter_keys(k_all));
  auto all_filtered_by_m234 = tc.root.add_root(all->filter_keys(k_m234));

  auto m56_filtered_by_m135 = tc.root.add_root(m56->filter_keys(k_m135));
  auto m135_filtered_by_m56 = tc.root.add_root(m135->filter_keys(k_m56));

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_filtered_by_empty, ElementsAre());
  EXPECT_THAT(*empty_filtered_by_m234, ElementsAre());
  EXPECT_THAT(*m234_filtered_by_empty, ElementsAre());

  EXPECT_THAT(*m234_filtered_by_m234,
              ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*m234_filtered_by_m56, ElementsAre());
  EXPECT_THAT(*m56_filtered_by_m234, ElementsAre());
  EXPECT_THAT(*m234_filtered_by_m135, ElementsAre(MP(3, 234)));
  EXPECT_THAT(*m135_filtered_by_m234, ElementsAre(MP(3, 135)));
  EXPECT_THAT(*m234_filtered_by_all,
              ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*all_filtered_by_m234,
              ElementsAre(MP(2, 123456), MP(3, 123456), MP(4, 123456)));

  EXPECT_THAT(*m56_filtered_by_m135, ElementsAre(MP(5, 56)));
  EXPECT_THAT(*m135_filtered_by_m56, ElementsAre(MP(5, 135)));
}

TEST(ManagedMapTest, Difference) {
  TestContext tc;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> empty;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> all;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m234;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m56;
  managed_ptr<ManagedMap<ManagedInt, ManagedDouble>> m135;

  {
    auto hold = tc.mgr.acquire_hold();
    empty = managed_map<ManagedInt, ManagedDouble>();
    all = emplace(*empty, 1, 123456).first;
    all = emplace(*all, 2, 123456).first;
    all = emplace(*all, 3, 123456).first;
    all = emplace(*all, 4, 123456).first;
    all = emplace(*all, 5, 123456).first;
    all = emplace(*all, 6, 123456).first;
    m234 = emplace(*empty, 2, 234).first;
    m234 = emplace(*m234, 3, 234).first;
    m234 = emplace(*m234, 4, 234).first;
    m56 = emplace(*empty, 5, 56).first;
    m56 = emplace(*m56, 6, 56).first;
    m135 = emplace(*empty, 1, 135).first;
    m135 = emplace(*m135, 3, 135).first;
    m135 = emplace(*m135, 5, 135).first;
    tc.root.add_root(empty);
    tc.root.add_root(all);
    tc.root.add_root(m234);
    tc.root.add_root(m56);
    tc.root.add_root(m135);
  }
  auto empty_minus_empty = tc.root.add_root(empty - empty);
  auto empty_minus_m234 = tc.root.add_root(empty - m234);
  auto m234_minus_empty = tc.root.add_root(m234 - empty);

  auto m234_minus_m234 = tc.root.add_root(m234 - m234);
  auto m234_minus_m56 = tc.root.add_root(m234 - m56);
  auto m56_minus_m234 = tc.root.add_root(m56 - m234);
  auto m234_minus_m135 = tc.root.add_root(m234 - m135);
  auto m135_minus_m234 = tc.root.add_root(m135 - m234);
  auto m234_minus_all = tc.root.add_root(m234 - all);
  auto all_minus_m234 = tc.root.add_root(all - m234);

  auto m56_minus_m135 = tc.root.add_root(m56 - m135);
  auto m135_minus_m56 = tc.root.add_root(m135 - m56);

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(*empty_minus_empty, ElementsAre());
  EXPECT_THAT(*empty_minus_m234, ElementsAre());
  EXPECT_THAT(*m234_minus_empty,
              ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));

  EXPECT_THAT(*m234_minus_m234, ElementsAre());
  EXPECT_THAT(*m234_minus_m56, ElementsAre(MP(2, 234), MP(3, 234), MP(4, 234)));
  EXPECT_THAT(*m56_minus_m234, ElementsAre(MP(5, 56), MP(6, 56)));
  EXPECT_THAT(*m234_minus_m135, ElementsAre(MP(2, 234), MP(4, 234)));
  EXPECT_THAT(*m135_minus_m234, ElementsAre(MP(1, 135), MP(5, 135)));
  EXPECT_THAT(*m234_minus_all, ElementsAre());
  EXPECT_THAT(*all_minus_m234,
              ElementsAre(MP(1, 123456), MP(5, 123456), MP(6, 123456)));

  EXPECT_THAT(*m56_minus_m135, ElementsAre(MP(6, 56)));
  EXPECT_THAT(*m135_minus_m56, ElementsAre(MP(1, 135), MP(3, 135)));
}

TEST(ManagedMapTest, Stress) {
  std::random_device rand_dev;
  std::mt19937 generator(rand_dev());
  std::uniform_int_distribution<int> dist(-128, 127);
  // remap instead of erase a quarter of the time
  std::bernoulli_distribution coin_flip(0.25);

  TestContext tc;
  auto prev = tc.root.add_root(managed_map<ManagedInt, ManagedInt>());
  for (int run = 0; run < 2; ++run) {
    int num_erasures = 0;
    int num_remaps = 0;
    int num_inserts = 0;

    auto m =
        tc.root.add_root(make_managed<ManagedMap<ManagedInt, ManagedInt>>());
    std::size_t size = 0;
    for (int i = 0; i < 1000; ++i) {
      const int key = dist(generator);
      if (m->contains(key)) {
        const int prev_val = (*m->get(key))->n;
        ASSERT_THAT(prev_val, AnyOf(Eq(key), Eq(-key)));
        ASSERT_EQ(*m->find(key), MP(key, prev_val));
        if (coin_flip(generator)) {
          // remap
          auto insert_result =
              m->emplace(std::make_tuple(key), std::make_tuple(-prev_val));
          ASSERT_EQ(insert_result.second, prev_val);
          ASSERT_NE(insert_result.first, m);
          m = tc.root.replace_root(m, insert_result.first);
          ++num_remaps;
        } else {
          // erase
          auto erase_result = m->erase(key);
          ASSERT_EQ(erase_result.second, prev_val);
          ASSERT_NE(erase_result.first, m);
          m = tc.root.replace_root(m, erase_result.first);
          --size;
          ++num_erasures;
        }
      } else {
        auto erase_result = m->erase(key);
        ASSERT_FALSE(erase_result.second);
        ASSERT_EQ(erase_result.first, m);
        auto insert_result =
            m->emplace(std::make_tuple(key), std::make_tuple(-key));
        ASSERT_FALSE(insert_result.second);
        ASSERT_NE(insert_result.first, m);
        m = tc.root.replace_root(m, insert_result.first);
        ASSERT_TRUE(m->contains(key));
        ASSERT_EQ(m->get(key), -key);
        ASSERT_EQ(*m->find(key), MP(key, -key));
        ++size;
        ++num_inserts;
      }
      ASSERT_EQ(m->size(), size);
      {
        auto hold = tc.mgr.acquire_hold();
        ASSERT_THAT(*m, BeginEndDistanceIs(size));
      }
      ASSERT_EQ(m->empty(), size == 0);
      ManagedMapAccessor::verify_invariants(*m);
    }
    ASSERT_GT(num_inserts, 50);
    ASSERT_GT(num_remaps, 50);
    ASSERT_GT(num_erasures, 50);
    auto u1 = tc.root.add_root(prev | m);
    auto u2 = tc.root.add_root(m | prev);
    ManagedMapAccessor::verify_invariants(*u1);
    ManagedMapAccessor::verify_invariants(*u2);
    auto i1 = tc.root.add_root(prev & m);
    auto i2 = tc.root.add_root(m & prev);
    ManagedMapAccessor::verify_invariants(*i1);
    ManagedMapAccessor::verify_invariants(*i2);
    auto d1 = tc.root.add_root(prev - m);
    auto d2 = tc.root.add_root(m - prev);
    ManagedMapAccessor::verify_invariants(*d1);
    ManagedMapAccessor::verify_invariants(*d2);
    {
      auto hold = tc.mgr.acquire_hold();
      ASSERT_THAT(*u1, BeginEndDistanceIs(u1->size()));
      ASSERT_THAT(*u2, BeginEndDistanceIs(u2->size()));
      for (const auto& el : *m) {
        ASSERT_EQ(u1->get(*el.first), el.second);
        if (prev->contains(*el.first)) {
          ASSERT_EQ(u2->get(*el.first), prev->get(*el.first));
        } else {
          ASSERT_EQ(u2->get(*el.first), el.second);
        }
      }
      for (const auto& el : *prev) {
        ASSERT_EQ(u2->get(*el.first), el.second);
        if (m->contains(*el.first)) {
          ASSERT_EQ(u1->get(*el.first), m->get(*el.first));
        } else {
          ASSERT_EQ(u1->get(*el.first), el.second);
        }
      }
      for (const auto& el : *u1) {
        ASSERT_TRUE(m->contains(*el.first) || prev->contains(*el.first));
      }
      for (const auto& el : *u2) {
        ASSERT_TRUE(m->contains(*el.first) || prev->contains(*el.first));
      }

      ASSERT_THAT(*i1, BeginEndDistanceIs(i1->size()));
      ASSERT_THAT(*i2, BeginEndDistanceIs(i2->size()));
      for (const auto& el : *m) {
        if (prev->contains(*el.first)) {
          ASSERT_EQ(i1->get(*el.first), el.second);
          ASSERT_EQ(i2->get(*el.first), prev->get(*el.first));
        } else {
          ASSERT_FALSE(i1->contains(*el.first));
          ASSERT_FALSE(i2->contains(*el.first));
        }
      }
      for (const auto& el : *prev) {
        if (m->contains(*el.first)) {
          ASSERT_EQ(i1->get(*el.first), m->get(*el.first));
          ASSERT_EQ(i2->get(*el.first), el.second);
        } else {
          ASSERT_FALSE(i1->contains(*el.first));
          ASSERT_FALSE(i2->contains(*el.first));
        }
      }
      for (const auto& el : *i1) {
        ASSERT_TRUE(m->contains(*el.first) && prev->contains(*el.first));
      }
      for (const auto& el : *i2) {
        ASSERT_TRUE(m->contains(*el.first) && prev->contains(*el.first));
      }

      ASSERT_THAT(*d1, BeginEndDistanceIs(d1->size()));
      ASSERT_THAT(*d2, BeginEndDistanceIs(d2->size()));
      for (const auto& el : *m) {
        if (prev->contains(*el.first)) {
          ASSERT_FALSE(d1->contains(*el.first));
          ASSERT_FALSE(d2->contains(*el.first));
        } else {
          ASSERT_FALSE(d1->contains(*el.first));
          ASSERT_EQ(d2->get(*el.first), el.second);
        }
      }
      for (const auto& el : *prev) {
        if (m->contains(*el.first)) {
          ASSERT_FALSE(d1->contains(*el.first));
          ASSERT_FALSE(d2->contains(*el.first));
        } else {
          ASSERT_EQ(d1->get(*el.first), el.second);
          ASSERT_FALSE(d2->contains(*el.first));
        }
      }
      for (const auto& el : *d1) {
        ASSERT_TRUE(!m->contains(*el.first) && prev->contains(*el.first));
      }
      for (const auto& el : *d2) {
        ASSERT_TRUE(m->contains(*el.first) && !prev->contains(*el.first));
      }
      prev = m;
    }
  }
}

#undef MP

}  // namespace emil::collections::testing
