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

#include "emil/gc.h"

#include <gtest/gtest.h>

#include <new>
#include <string>

#include "testing/test_util.h"

namespace emil::testing {
namespace {

using Stats = MemoryManager::Stats;

class SimpleManaged : public Managed {
 public:
  bool& alive;

  explicit SimpleManaged(bool& alive) : alive(alive) { alive = true; }
  ~SimpleManaged() override { alive = false; }
  std::size_t managed_size() const noexcept override {
    return sizeof(SimpleManaged);
  }

 private:
  void visit_subobjects(const ManagedVisitor&) override {}
};

class SimpleManagedWithSelfPtr
    : public ManagedWithSelfPtr<SimpleManagedWithSelfPtr> {
 public:
  bool& alive;

  explicit SimpleManagedWithSelfPtr(bool& alive) : alive(alive) {
    alive = true;
  }
  ~SimpleManagedWithSelfPtr() override { alive = false; }

  const managed_ptr<SimpleManagedWithSelfPtr>& get_self() const {
    return self();
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(SimpleManagedWithSelfPtr);
  }

 private:
  void visit_subobjects(const ManagedVisitor&) override {}
};

template <ManagedType L, ManagedType R>
class ManagedPair : public Managed {
 public:
  bool& alive;

  ManagedPair(bool& alive, managed_ptr<L> l, managed_ptr<R> r)
      : alive(alive), l_(std::move(l)), r_(std::move(r)) {
    alive = true;
  }
  ~ManagedPair() override { alive = false; }

  managed_ptr<L> left() const { return l_; }
  managed_ptr<R> right() const { return r_; }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedPair);
  }

 private:
  managed_ptr<L> l_;
  managed_ptr<R> r_;

  void visit_subobjects(const ManagedVisitor& v) override {
    l_.accept(v);
    r_.accept(v);
  }
};

struct Payload {
  bool& alive;
  int foo;
  double bar;

  Payload(bool& alive, int foo, double bar) : alive(alive), foo(foo), bar(bar) {
    alive = true;
  }
  ~Payload() { alive = false; }
};

[[maybe_unused]] bool operator==(const Payload& l, const Payload& r) {
  return l.foo == r.foo && l.bar == r.bar;
}

class ManagedPayload : public Managed {
 public:
  bool& alive;

  ManagedPayload(MemoryManager& mgr, bool& alive, bool& payload_alive, int foo,
                 double bar)
      : alive(alive), buf(mgr.allocate_private_buffer(sizeof(Payload))) {
    alive = true;
    new (buf.buf()) Payload(payload_alive, foo, bar);
  }

  ~ManagedPayload() {
    alive = false;
    payload()->~Payload();
  }

  Payload* payload() { return reinterpret_cast<Payload*>(buf.buf()); }

 private:
  PrivateBuffer buf;

  void visit_subobjects(const ManagedVisitor&) override {}
  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedPayload);
  }
};

TEST(GcTest, OneObject) {
  bool alive = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));
    auto ptr = root.add_root(mgr.create<SimpleManaged>(alive));
    ASSERT_TRUE(alive);
    ASSERT_TRUE(ptr->alive);
    ASSERT_EQ(mgr.stats(), (Stats{sizeof(SimpleManaged), 1, 0}));
  }
  ASSERT_FALSE(alive);
}

TEST(GcTest, TwoObjects) {
  bool alive1 = false;
  bool alive2 = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));
    auto ptr1 = root.add_root(mgr.create<SimpleManaged>(alive1));
    auto ptr2 = root.add_root(mgr.create<SimpleManaged>(alive2));
    ASSERT_TRUE(alive1);
    ASSERT_TRUE(ptr1->alive);
    ASSERT_TRUE(alive2);
    ASSERT_TRUE(ptr2->alive);
    ASSERT_EQ(mgr.stats(), (Stats{2 * sizeof(SimpleManaged), 2, 0}));
  }
  ASSERT_FALSE(alive1);
  ASSERT_FALSE(alive2);
}

TEST(GcTest, FreesUnreachableObjectsWithHolds) {
  bool alive1 = false;
  bool alive2 = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));

    auto ptr1 = mgr.create<SimpleManaged>(alive1);
    ASSERT_TRUE(alive1);
    ASSERT_TRUE(ptr1->alive);
    ASSERT_EQ(mgr.stats(), (Stats{sizeof(SimpleManaged), 1}));

    auto ptr2 = root.add_root(mgr.create<SimpleManaged>(alive2));
    ASSERT_FALSE(alive1);
    ASSERT_TRUE(alive2);
    ASSERT_TRUE(ptr2->alive);
    EXPECT_EQ(mgr.stats(), (Stats{sizeof(SimpleManaged), 1}));

    ptr1 = mgr.create<SimpleManaged>(alive1);
    ASSERT_TRUE(alive1);
    ASSERT_TRUE(ptr1->alive);
    ASSERT_TRUE(alive2);
    ASSERT_TRUE(ptr2->alive);
    EXPECT_EQ(mgr.stats(), (Stats{2 * sizeof(SimpleManaged), 2}));
  }
  EXPECT_FALSE(alive1);
  EXPECT_FALSE(alive2);
}

TEST(GcTest, HoldsPreventObjectFreeing) {
  bool alive1 = false;
  bool alive2 = false;
  bool alive3 = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    {
      ASSERT_EQ(mgr.stats(), (Stats{}));

      auto ptr1 = mgr.create<SimpleManaged>(alive1);
      ASSERT_TRUE(alive1);
      ASSERT_TRUE(ptr1->alive);
      ASSERT_EQ(mgr.stats(), (Stats{sizeof(SimpleManaged), 1}));

      auto hold = mgr.acquire_hold();
      ASSERT_FALSE(alive1);
      ASSERT_EQ(mgr.stats(), (Stats{.num_holds = 1}));

      ptr1 = mgr.create<SimpleManaged>(alive1);
      ASSERT_TRUE(alive1);
      ASSERT_TRUE(ptr1->alive);
      ASSERT_EQ(mgr.stats(), (Stats{sizeof(SimpleManaged), 1, 0, 1}));

      auto ptr2 = root.add_root(mgr.create<SimpleManaged>(alive2));
      ASSERT_TRUE(alive1);
      ASSERT_TRUE(ptr1->alive);
      ASSERT_TRUE(alive2);
      ASSERT_TRUE(ptr2->alive);
      EXPECT_EQ(mgr.stats(), (Stats{2 * sizeof(SimpleManaged), 2, 0, 1}));

      auto hold2 = std::move(hold);
      ASSERT_EQ(mgr.stats(), (Stats{2 * sizeof(SimpleManaged), 2, 0, 1}));

      ptr1 = mgr.create<SimpleManaged>(alive3);
      ASSERT_TRUE(alive1);
      ASSERT_TRUE(alive2);
      ASSERT_TRUE(ptr2->alive);
      ASSERT_TRUE(alive3);
      ASSERT_TRUE(ptr1->alive);
      EXPECT_EQ(mgr.stats(), (Stats{3 * sizeof(SimpleManaged), 3, 0, 1}));
    }
    EXPECT_EQ(mgr.stats(), (Stats{3 * sizeof(SimpleManaged), 3, 0, 0}));
  }
  EXPECT_FALSE(alive1);
  EXPECT_FALSE(alive2);
  EXPECT_FALSE(alive3);
}

class CountingVisitor : public ManagedVisitor {
 public:
  explicit CountingVisitor(int& count) : count_(count) {}

 private:
  int& count_;
  bool visit(managed_ptr_base&) const override {
    ++count_;
    return true;
  }
};

TEST(GcTest, Tree) {
  bool alive_root = false;
  bool alive_l = false;
  bool alive_ll = false;
  bool alive_lr = false;
  bool alive_r = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));
    using RootType =
        ManagedPair<ManagedPair<SimpleManaged, SimpleManaged>, SimpleManaged>;
    managed_ptr<RootType> tree_root;
    {
      auto hold = mgr.acquire_hold();
      tree_root = root.add_root(mgr.create<RootType>(
          alive_root,
          mgr.create<ManagedPair<SimpleManaged, SimpleManaged>>(
              alive_l, mgr.create<SimpleManaged>(alive_ll),
              mgr.create<SimpleManaged>(alive_lr)),
          mgr.create<SimpleManaged>(alive_r)));
    }
    ASSERT_TRUE(alive_root);
    ASSERT_TRUE(tree_root->alive);
    ASSERT_TRUE(alive_l);
    ASSERT_TRUE(tree_root->left()->alive);
    ASSERT_TRUE(alive_ll);
    ASSERT_TRUE(tree_root->left()->left()->alive);
    ASSERT_TRUE(alive_lr);
    ASSERT_TRUE(tree_root->left()->right()->alive);
    ASSERT_TRUE(alive_r);
    ASSERT_TRUE(tree_root->right()->alive);
    ASSERT_EQ(mgr.stats(), (Stats{tree_root->managed_size() +
                                      tree_root->left()->managed_size() +
                                      3 * sizeof(SimpleManaged),
                                  5, 0}));
    int count = 0;
    tree_root.accept(CountingVisitor(count));
    ASSERT_EQ(count, 5);
  }
  ASSERT_FALSE(alive_root);
  ASSERT_FALSE(alive_l);
  ASSERT_FALSE(alive_ll);
  ASSERT_FALSE(alive_lr);
  ASSERT_FALSE(alive_r);
}

TEST(GcTest, SelfPtr) {
  bool alive;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));
    auto ptr = root.add_root(mgr.create<SimpleManagedWithSelfPtr>(alive));
    ASSERT_TRUE(alive);
    ASSERT_TRUE(ptr->alive);
    ASSERT_TRUE(ptr->get_self());
    ASSERT_TRUE(ptr->get_self()->alive);
    ASSERT_EQ(mgr.stats(), (Stats{sizeof(SimpleManagedWithSelfPtr), 1, 0}));
  }
  ASSERT_FALSE(alive);
}

TEST(GcTest, PrivateBuffer) {
  bool alive_outer = false;
  bool alive_inner = false;
  {
    TestRoot root;
    MemoryManager mgr(root);
    ASSERT_EQ(mgr.stats(), (Stats{}));
    auto ptr = root.add_root(
        mgr.create<ManagedPayload>(mgr, alive_outer, alive_inner, 42, 2.5));
    ASSERT_TRUE(alive_outer);
    ASSERT_TRUE(alive_inner);
    bool alive_tmp = false;
    ASSERT_EQ(mgr.stats(),
              (Stats{sizeof(ManagedPayload) + sizeof(Payload), 1, 1}));
    ASSERT_EQ(*ptr->payload(), (Payload{alive_tmp, 42, 2.5}));
  }
  ASSERT_FALSE(alive_outer);
  ASSERT_FALSE(alive_inner);
}

TEST(GcTest, Bool) {
  TestRoot root;
  MemoryManager mgr(root);
  bool alive = false;
  auto true_ptr = root.add_root(mgr.create<SimpleManaged>(alive));
  managed_ptr<SimpleManaged> false_ptr = nullptr;

  if (true_ptr) {
    SUCCEED();
  } else {
    FAIL() << "Expected pointer to evaluate to true.";
  }

  if (false_ptr) {
    FAIL() << "Expected pointer to evaluate to false.";
  } else {
    SUCCEED();
  }
}

}  // namespace
}  // namespace emil::testing
