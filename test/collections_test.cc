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
#include <string>
#include <vector>

#include "emil/gc.h"
#include "emil/runtime.h"
#include "testing/test_util.h"

namespace emil::collections::testing {

using TestContext = emil::testing::TestContext;
using ::testing::AnyOf;
using ::testing::ElementsAre;
using ::testing::Eq;

class ManagedSetAccessor {
 public:
  template <ManagedType T, typename Comp>
  static void verify_invariants(const ManagedSet<T, Comp>& set) {
    auto hold = ctx().mgr->acquire_hold();
    detail::verify_invariants(set.tree_, *set.comp_);
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
    detail::verify_invariants(map.tree_, *map.comp_);
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

TEST(ConsTest, Cons) {
  TestContext tc;
  auto l = tc.root.add_root(cons_in_place<ManagedInt>(nullptr, 1));
  auto i = tc.root.add_root(mi(2));
  l = tc.root.replace_root(l, cons(i, l));
  tc.root.remove_root(i);
  l = tc.root.replace_root(l, cons_in_place(l, 3));
  l = tc.root.replace_root(l, cons(nullptr, l));
  ASSERT_FALSE(l->car);
  ASSERT_EQ(l->cdr->car, 3);
  ASSERT_EQ(l->cdr->cdr->car, 2);
  ASSERT_EQ(l->cdr->cdr->cdr->car, 1);
  ASSERT_FALSE(l->cdr->cdr->cdr->cdr);
}

TEST(ManagedSetTest, OrderedAfterInserts) {
  TestContext tc;

  auto s =
      tc.root.add_root(make_managed<ManagedSet<ManagedInt, managed_int_less>>(
          managed_int_less{}));
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

  managed_ptr<ManagedSet<ManagedInt, managed_int_less>> full_set;
  {
    auto hold = tc.mgr.acquire_hold();
    full_set = tc.root.add_root(managed_set(
        managed_int_less{}, {mi(1), mi(2), mi(3), mi(4), mi(5), mi(6), mi(7)}));
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

  auto empty_set =
      tc.root.add_root(managed_set<ManagedInt>(managed_int_less{}, {}));
  result = empty_set->erase(3);
  ASSERT_FALSE(result.second);
  ASSERT_EQ(result.first, empty_set);
  ManagedSetAccessor::verify_invariants(*empty_set);
  auto hold = tc.mgr.acquire_hold();
  ASSERT_THAT(*empty_set, ElementsAre());
  ASSERT_THAT(*s, ElementsAre(2, 4, 6));
  ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, StressTest) {
  std::random_device rand_dev;
  std::mt19937 generator(rand_dev());
  std::uniform_int_distribution<int> dist(-128, 127);

  TestContext tc;
  for (int run = 0; run < 2; ++run) {
    auto s = tc.root.add_root(
        make_managed<ManagedSet<ManagedInt, managed_int_less>>());
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
        ASSERT_THAT(*s, ::testing::BeginEndDistanceIs(size));
      }
      ASSERT_EQ(s->empty(), size == 0);
      ManagedSetAccessor::verify_invariants(*s);
    }
  }
}

std::pair<managed_ptr<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>>,
          std::optional<managed_ptr<ManagedDouble>>>
emplace(const ManagedMap<ManagedInt, ManagedDouble, managed_int_less>& m, int i,
        double d) {
  return m.emplace(std::make_tuple(i), std::make_tuple(d));
}

#define MP(x, y) std::make_pair(x, y)

TEST(ManagedMapTest, OrderedAfterInserts) {
  TestContext tc;

  auto m = tc.root.add_root(
      make_managed<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>>());
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
  auto m = tc.root.add_root(
      make_managed<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>>());
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

  managed_ptr<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>> full_map;
  {
    auto hold = tc.mgr.acquire_hold();
    full_map = tc.root.add_root(
        managed_map(managed_int_less{}, {
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

  auto empty_map = tc.root.add_root(
      managed_map<ManagedInt, ManagedDouble>(managed_int_less{}, {}));
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

TEST(ManagedMapTest, StressTest) {
  std::random_device rand_dev;
  std::mt19937 generator(rand_dev());
  std::uniform_int_distribution<int> dist(-128, 127);
  // remap instead of erase a quarter of the time
  std::bernoulli_distribution coin_flip(0.25);

  TestContext tc;
  for (int run = 0; run < 2; ++run) {
    int num_erasures = 0;
    int num_remaps = 0;
    int num_inserts = 0;

    auto m = tc.root.add_root(
        make_managed<ManagedMap<ManagedInt, ManagedInt, managed_int_less>>());
    std::size_t size = 0;
    for (int i = 0; i < 1000; ++i) {
      const int key = dist(generator);
      if (m->contains(key)) {
        const int prev = (*m->get(key))->n;
        ASSERT_THAT(prev, AnyOf(Eq(key), Eq(-key)));
        ASSERT_EQ(*m->find(key), MP(key, prev));
        if (coin_flip(generator)) {
          // remap
          auto insert_result =
              m->emplace(std::make_tuple(key), std::make_tuple(-prev));
          ASSERT_EQ(insert_result.second, prev);
          ASSERT_NE(insert_result.first, m);
          m = tc.root.replace_root(m, insert_result.first);
          ++num_remaps;
        } else {
          // erase
          auto erase_result = m->erase(key);
          ASSERT_EQ(erase_result.second, prev);
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
        ASSERT_THAT(*m, ::testing::BeginEndDistanceIs(size));
      }
      ASSERT_EQ(m->empty(), size == 0);
      ManagedMapAccessor::verify_invariants(*m);
    }
    ASSERT_GT(num_inserts, 50);
    ASSERT_GT(num_remaps, 50);
    ASSERT_GT(num_erasures, 50);
  }
}

#undef MP

}  // namespace emil::collections::testing
