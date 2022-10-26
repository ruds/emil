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
#include "testing/test_util.h"

namespace emil::collections::testing {

using TestRoot = emil::testing::TestRoot;
using ::testing::AnyOf;
using ::testing::ElementsAre;
using ::testing::Eq;

class ManagedSetAccessor {
 public:
  template <ManagedType T, typename Comp>
  static void verify_invariants(const ManagedSet<T, Comp>& set) {
    auto hold = set.mgr_->acquire_hold();
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
    auto hold = map.mgr_->acquire_hold();
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

managed_ptr<ManagedInt> mi(MemoryManager& mgr, int n) {
  return mgr.create<ManagedInt>(n);
}

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

managed_ptr<ManagedDouble> md(MemoryManager& mgr, double d) {
  return mgr.create<ManagedDouble>(d);
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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre());
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1));
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 5));
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 4, 5));
  }

  auto s145 = s;

  s = root.add_root(s->emplace(2).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 4, 5));
    ASSERT_THAT(*s145, ElementsAre(1, 4, 5)) << "ManagedSet is not persistent.";
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5));
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6));
  }

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
  {
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  std::vector<managed_ptr<ManagedInt>> v;
  auto hold = mgr.acquire_hold();
  std::copy(s->begin(), s->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
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
  ManagedSetAccessor::verify_invariants(*s);
  EXPECT_THAT(*s, ElementsAre(1, 2, 3));

  auto s2 =
      managed_set(mgr, std::greater<>(), {mi(mgr, 1), mi(mgr, 3), mi(mgr, 2)});
  ManagedSetAccessor::verify_invariants(*s2);
  EXPECT_THAT(*s2, ElementsAre(3, 2, 1));
}

TEST(ManagedSetTest, OrderedAfterDeletions) {
  TestRoot root;
  MemoryManager mgr(root);

  managed_ptr<ManagedSet<ManagedInt, managed_int_less>> full_set;
  {
    auto hold = mgr.acquire_hold();
    full_set = root.add_root(
        managed_set(mgr, managed_int_less{},
                    {mi(mgr, 1), mi(mgr, 2), mi(mgr, 3), mi(mgr, 4), mi(mgr, 5),
                     mi(mgr, 6), mi(mgr, 7)}));
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(1, 2, 3, 4, 5, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = full_set->erase(1);
  s = root.add_root(result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 5, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(5);
  s = root.replace_root(s, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 6, 7));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(7);
  s = root.replace_root(s, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 3, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(3);
  s = root.replace_root(s, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  result = s->erase(3);
  s = root.replace_root(s, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*s, ElementsAre(2, 4, 6));
    ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
  }

  auto empty_set =
      root.add_root(managed_set<ManagedInt>(mgr, managed_int_less{}, {}));
  result = empty_set->erase(3);
  ASSERT_FALSE(result.second);
  ASSERT_EQ(result.first, empty_set);
  ManagedSetAccessor::verify_invariants(*empty_set);
  auto hold = mgr.acquire_hold();
  ASSERT_THAT(*empty_set, ElementsAre());
  ASSERT_THAT(*s, ElementsAre(2, 4, 6));
  ASSERT_THAT(*full_set, ElementsAre(1, 2, 3, 4, 5, 6, 7));
}

TEST(ManagedSetTest, StressTest) {
  std::random_device rand_dev;
  std::mt19937 generator(rand_dev());
  std::uniform_int_distribution<int> dist(-128, 127);

  TestRoot root;
  MemoryManager mgr(root);
  for (int run = 0; run < 2; ++run) {
    auto s = root.add_root(
        mgr.create<ManagedSet<ManagedInt, managed_int_less>>(mgr));
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
        s = root.replace_root(s, erase_result.first);
        ASSERT_FALSE(s->contains(num));
        --size;
      } else {
        auto erase_result = s->erase(num);
        ASSERT_FALSE(erase_result.second);
        ASSERT_EQ(erase_result.first, s);
        auto insert_result = s->emplace(num);
        ASSERT_TRUE(insert_result.second);
        ASSERT_NE(insert_result.first, s);
        s = root.replace_root(s, insert_result.first);
        ASSERT_TRUE(s->contains(num));
        ASSERT_EQ(*s->find(num), num);
        ++size;
      }
      ASSERT_EQ(s->size(), size);
      {
        auto hold = mgr.acquire_hold();
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
  TestRoot root;
  MemoryManager mgr(root);

  auto m = root.add_root(
      mgr.create<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>>(mgr));
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre());
  }

  m = root.replace_root(m, emplace(*m, 1, -1.0).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0)));
  }

  m = root.replace_root(m, emplace(*m, 5, -2.3).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(5, -2.3)));
  }

  m = root.replace_root(m, emplace(*m, 4, 1e5).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(4, 1e5), MP(5, -2.3)));
  }

  auto m145 = m;

  m = root.add_root(emplace(*m, 2, 4.25).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(4, 1e5), MP(5, -2.3)));
    ASSERT_THAT(*m145, ElementsAre(MP(1, -1.0), MP(4, 1e5), MP(5, -2.3)))
        << "ManagedMap is not persistent";
  }

  m = root.replace_root(m, emplace(*m, 3, 1e-14).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14),
                                MP(4, 1e5), MP(5, -2.3)));
  }

  m = root.replace_root(m, emplace(*m, 6, 3.14).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14),
                                MP(4, 1e5), MP(5, -2.3), MP(6, 3.14)));
  }

  m = root.replace_root(m, emplace(*m, 7, 2.718).first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                            MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
  }

  std::vector<std::pair<managed_ptr<ManagedInt>, managed_ptr<ManagedDouble>>> v;
  auto hold = mgr.acquire_hold();
  std::copy(m->begin(), m->end(), std::back_inserter(v));
  ASSERT_THAT(v, ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                             MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
  ASSERT_THAT(*m,
              ElementsAre(MP(1, -1.0), MP(2, 4.25), MP(3, 1e-14), MP(4, 1e5),
                          MP(5, -2.3), MP(6, 3.14), MP(7, 2.718)));
}

TEST(ManagedMapTest, HandlesRemapping) {
  TestRoot root;
  MemoryManager mgr(root);
  auto m = root.add_root(
      mgr.create<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>>(mgr));
  ManagedMapAccessor::verify_invariants(*m);
  EXPECT_FALSE(m->get(1));

  auto r = emplace(*m, 1, 1.0);
  EXPECT_NE(m, r.first);
  root.add_root(r.first);
  EXPECT_FALSE(r.second);
  ManagedMapAccessor::verify_invariants(*m);
  ManagedMapAccessor::verify_invariants(*r.first);
  root.remove_root(m);
  m = r.first;
  EXPECT_EQ(m->get(1), 1.0);
  EXPECT_EQ(*m->find(1), MP(1, 1.0));

  r = emplace(*m, 1, -1.0);
  EXPECT_NE(m, r.first);
  root.add_root(r.first);
  EXPECT_EQ(r.second, 1);
  ManagedMapAccessor::verify_invariants(*m);
  ManagedMapAccessor::verify_invariants(*r.first);
  EXPECT_EQ(m->get(1), 1.0);
  EXPECT_EQ(*m->find(1), MP(1, 1.0));
  EXPECT_EQ(r.first->get(1), -1.0);
  EXPECT_EQ(*r.first->find(1), MP(1, -1.0));

  auto hold = mgr.acquire_hold();
  ASSERT_THAT(*m, ElementsAre(MP(1, 1.0)));
  ASSERT_THAT(*r.first, ElementsAre(MP(1, -1.0)));
}

TEST(ManagedMapTest, Factories) {
  TestRoot root;
  MemoryManager mgr(root);
  auto hold = mgr.acquire_hold();

  auto m = managed_map(
      mgr, {MP(mi(mgr, 1), md(mgr, 1.0)), MP(mi(mgr, 3), md(mgr, 3.0)),
            MP(mi(mgr, 2), md(mgr, 2.0))});
  ManagedMapAccessor::verify_invariants(*m);
  EXPECT_THAT(*m, ElementsAre(MP(1, 1.0), MP(2, 2.0), MP(3, 3.0)));

  auto m2 =
      managed_map(mgr, std::greater<>(),
                  {MP(mi(mgr, 1), md(mgr, 1.0)), MP(mi(mgr, 3), md(mgr, 3.0)),
                   MP(mi(mgr, 2), md(mgr, 2.0))});
  ManagedMapAccessor::verify_invariants(*m2);
  EXPECT_THAT(*m2, ElementsAre(MP(3, 3.0), MP(2, 2.0), MP(1, 1.0)));
}

TEST(ManagedMapTest, OrderedAfterDeletions) {
  TestRoot root;
  MemoryManager mgr(root);

  managed_ptr<ManagedMap<ManagedInt, ManagedDouble, managed_int_less>> full_map;
  {
    auto hold = mgr.acquire_hold();
    full_map = root.add_root(managed_map(mgr, managed_int_less{},
                                         {
                                             MP(mi(mgr, 1), md(mgr, -1.0)),
                                             MP(mi(mgr, 2), md(mgr, -2.0)),
                                             MP(mi(mgr, 3), md(mgr, -3.0)),
                                             MP(mi(mgr, 4), md(mgr, -4.0)),
                                             MP(mi(mgr, 5), md(mgr, -5.0)),
                                             MP(mi(mgr, 6), md(mgr, -6.0)),
                                             MP(mi(mgr, 7), md(mgr, -7.0)),
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = full_map->erase(1);
  m = root.add_root(result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                                MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(5);
  m = root.replace_root(m, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                                MP(6, -6.0), MP(7, -7.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(7);
  m = root.replace_root(m, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(
        *m, ElementsAre(MP(2, -2.0), MP(3, -3.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(3);
  m = root.replace_root(m, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  result = m->erase(3);
  m = root.replace_root(m, result.first);
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
    auto hold = mgr.acquire_hold();
    ASSERT_THAT(*m, ElementsAre(MP(2, -2.0), MP(4, -4.0), MP(6, -6.0)));
    ASSERT_THAT(*full_map,
                ElementsAre(MP(1, -1.0), MP(2, -2.0), MP(3, -3.0), MP(4, -4.0),
                            MP(5, -5.0), MP(6, -6.0), MP(7, -7.0)));
  }

  auto empty_map = root.add_root(
      managed_map<ManagedInt, ManagedDouble>(mgr, managed_int_less{}, {}));
  result = empty_map->erase(3);
  ASSERT_FALSE(result.second);
  ASSERT_EQ(result.first, empty_map);
  ManagedMapAccessor::verify_invariants(*empty_map);
  auto hold = mgr.acquire_hold();
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

  TestRoot root;
  MemoryManager mgr(root);
  for (int run = 0; run < 2; ++run) {
    int num_erasures = 0;
    int num_remaps = 0;
    int num_inserts = 0;

    auto m = root.add_root(
        mgr.create<ManagedMap<ManagedInt, ManagedInt, managed_int_less>>(mgr));
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
          m = root.replace_root(m, insert_result.first);
          ++num_remaps;
        } else {
          // erase
          auto erase_result = m->erase(key);
          ASSERT_EQ(erase_result.second, prev);
          ASSERT_NE(erase_result.first, m);
          m = root.replace_root(m, erase_result.first);
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
        m = root.replace_root(m, insert_result.first);
        ASSERT_TRUE(m->contains(key));
        ASSERT_EQ(m->get(key), -key);
        ASSERT_EQ(*m->find(key), MP(key, -key));
        ++size;
        ++num_inserts;
      }
      ASSERT_EQ(m->size(), size);
      {
        auto hold = mgr.acquire_hold();
        ASSERT_THAT(*m, ::testing::BeginEndDistanceIs(size));
      }
      ASSERT_EQ(m->empty(), size == 0);
      ManagedMapAccessor::verify_invariants(*m);
    }
    ASSERT_GT(num_inserts, 100);
    ASSERT_GT(num_remaps, 100);
    ASSERT_GT(num_erasures, 100);
  }
}

#undef MP

}  // namespace emil::collections::testing
