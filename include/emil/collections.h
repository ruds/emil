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
#include <optional>
#include <stdexcept>
#include <tuple>
#include <utility>

#include "emil/gc.h"
#include "emil/runtime.h"

/**
 * @file collections.h
 *
 * @brief Collections for memory-managed types.
 */

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

/** A fixed-size (mutable) array. */
template <ManagedType T>
class ManagedArray : public Managed {
 public:
  using iterator = managed_ptr<T>*;
  using const_iterator = const managed_ptr<T>*;
  using reverse_iterator = std::reverse_iterator<iterator>;
  using const_reverse_iterator = std::reverse_iterator<const_iterator>;
  using value_type = managed_ptr<T>;
  using reference = managed_ptr<T>&;
  using const_reference = const managed_ptr<T>&;
  using pointer = managed_ptr<T>*;
  using const_pointer = const managed_ptr<T>*;

  ManagedArray() : buf_() {}

  /** Create an array of `len` nullptrs. */
  explicit ManagedArray(std::size_t len)
      : ManagedArray(len, [](std::size_t) { return nullptr; }) {}

  ManagedArray(std::initializer_list<managed_ptr<T>> els)
      : ManagedArray(els.size(),
                     [&els](std::size_t i) { return std::data(els)[i]; }) {}

  /**
   * Initialize the `len` elements of the array with `initializer`.
   *
   * The same instance of `initializer` is guaranteed to be called in order with
   * the arguments `0`, `1`, `2`, ..., `len - 1`.
   */
  template <typename F>
  ManagedArray(std::size_t len, F initializer) : buf_(allocate(len)) {
    for (std::size_t i = 0; i < len; ++i) {
      new (data() + i) managed_ptr<T>(initializer(i));
    }
  }

  bool empty() const { return buf_.size() == 0; }
  std::size_t size() const { return buf_.size() / sizeof(T); }

  managed_ptr<T>& operator[](std::size_t n) { return *(data() + n); }
  const managed_ptr<T>& operator[](std::size_t n) const {
    return *(data() + n);
  }

  managed_ptr<T>& at(std::size_t n) {
    if (size() <= n) throw std::out_of_range("Access out of bounds.");
    return (*this)[n];
  }

  const managed_ptr<T>& at(std::size_t n) const {
    if (size() <= n) throw std::out_of_range("Access out of bounds.");
    return (*this)[n];
  }

  iterator begin() { return data(); }
  const_iterator begin() const { return cbegin(); }

  iterator end() { return data() + size(); }
  const_iterator end() const { return cend(); }

  const_iterator cbegin() const { return data(); }

  const_iterator cend() const { return data() + size(); }

  reverse_iterator rbegin() { return std::reverse_iterator(end()); }
  const_reverse_iterator rbegin() const { return crbegin(); }

  reverse_iterator rend() { return std::reverse_iterator(begin()); }
  const_reverse_iterator rend() const { return crend(); }

  const_reverse_iterator crbegin() const {
    return std::reverse_iterator(cend());
  }

  const_reverse_iterator crend() const {
    return std::reverse_iterator(cbegin());
  }

 private:
  PrivateBuffer buf_;

  static PrivateBuffer allocate(std::size_t n) {
    return ctx().mgr->allocate_private_buffer(n * sizeof(T));
  }

  managed_ptr<T>* data() {
    return reinterpret_cast<managed_ptr<T>*>(buf_.buf());
  }

  const managed_ptr<T>* data() const {
    return reinterpret_cast<managed_ptr<T>*>(buf_.buf());
  }

  void visit_subobjects(const ManagedVisitor& visitor) override {
    std::for_each(begin(), end(),
                  [&visitor](managed_ptr<T>& t) { t.accept(visitor); });
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedArray);
  }
};

template <ManagedType T>
using ArrayPtr = managed_ptr<ManagedArray<T>>;

template <ManagedType T>
ArrayPtr<T> make_array(std::initializer_list<managed_ptr<T>> els) {
  return make_managed<ManagedArray<T>>(els);
}

namespace detail {

template <typename T, typename... Args>
requires std::is_constructible_v<T, Args...>
void is_constructible_from_tuple_impl(const std::tuple<Args...>&);

template <typename Tuple, typename T>
concept is_constructible_from_tuple = requires(const Tuple& t) {
  is_constructible_from_tuple_impl<T>(t);
};

}  // namespace detail

/** Construct elements of the new array using tuples as the constructor
 * arguments. */
template <ManagedType T, detail::is_constructible_from_tuple<T>... Tuples>
ArrayPtr<T> make_array(Tuples&&... tuples) {
  auto hold = ctx().mgr->acquire_hold();
  return make_array(
      {make_managed_from_tuple<T>(std::forward<Tuples>(tuples))...});
}

/**
 * Creates an array with the same elements as `list`.
 *
 * If `reverse_list` is false, the array is built in opposite order.
 */
template <ManagedType T>
ArrayPtr<T> to_array(ConsPtr<T> list, bool reverse_list = false) {
  const auto l = len(list);
  if (reverse_list) {
    auto arr = make_managed<ManagedArray<T>>(l);
    for (auto it = arr->rbegin(); it != arr->rend(); ++it) {
      *it = list->car;
      list = list->cdr;
    }
    return arr;
  } else {
    return make_managed<ManagedArray<T>>(l, [&list](std::size_t) mutable {
      auto p = list->car;
      list = list->cdr;
      return p;
    });
  }
}

namespace detail {

enum class Color {
  Red,    // Red nodes have no red children
  Black,  // Every path from a leaf to a given node has the same number of black
          // nodes
  DoubleBlack,  // Only used during the deletion algorithm -- counts
                // as two black nodes when computing black depth.
};

/** A red-black tree for managed types. */
template <ManagedType K, OptionalManagedType V = void>
struct ManagedTree;  // IWYU pragma: keep

template <ManagedType K, OptionalManagedType V = void>
using TreePtr = managed_ptr<ManagedTree<K, V>>;

/**
 * Trees with a key, used for sorting, and a side value, ignored for sorting.
 *
 * Null keys are not supported.
 */
template <ManagedType K, OptionalManagedType V>
struct ManagedTree : Managed {
  using payload_type = std::pair<managed_ptr<K>, managed_ptr<V>>;
  using value_type = managed_ptr<V>;
  using maybe_value_type = std::optional<managed_ptr<V>>;

  TreePtr<K, V> left;
  TreePtr<K, V> right;
  payload_type payload;
  Color color;

  static TreePtr<K, V> make_tree(TreePtr<K, V> left, TreePtr<K, V> right,
                                 payload_type payload, Color color) {
    return make_managed<ManagedTree<K, V>>(std::move(left), std::move(right),
                                           std::move(payload), color);
  }

  static const managed_ptr<K>& key(const payload_type& payload) {
    return payload.first;
  }

  static maybe_value_type maybe_value(value_type&& v) {
    return std::make_optional(std::move(v));
  }

  static maybe_value_type no_value() { return std::nullopt; }

  static TreePtr<K, V> double_black_empty() {
    return make_tree(nullptr, nullptr, {nullptr, nullptr}, Color::DoubleBlack);
  }

  const managed_ptr<K>& key() const { return payload.first; }

  const managed_ptr<V>& value() const { return payload.second; }

  ManagedTree(TreePtr<K, V>&& left, TreePtr<K, V>&& right,
              payload_type&& payload, Color color)
      : left(std::move(left)),
        right(std::move(right)),
        payload(std::move(payload)),
        color(color) {}

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (left) left.accept(visitor);
    if (right) right.accept(visitor);
    payload.first.accept(visitor);
    if (payload.second) payload.second.accept(visitor);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedTree);
  }
};

/**
 * Specialization for "sets" -- trees with just keys, no side values.
 *
 * Null keys are not supported.
 */
template <ManagedType K>
struct ManagedTree<K, void> : Managed {
  using payload_type = managed_ptr<K>;
  using value_type = bool;
  using maybe_value_type = bool;

  TreePtr<K, void> left;
  TreePtr<K, void> right;
  payload_type payload;
  Color color;

  static TreePtr<K> make_tree(TreePtr<K> left, TreePtr<K> right,
                              payload_type payload, Color color) {
    return make_managed<ManagedTree<K>>(std::move(left), std::move(right),
                                        std::move(payload), color);
  }

  static const managed_ptr<K>& key(const payload_type& payload) {
    return payload;
  }

  static bool maybe_value(bool v) { return v; }
  static bool no_value() { return false; }

  static TreePtr<K> double_black_empty() {
    return make_tree(nullptr, nullptr, nullptr, Color::DoubleBlack);
  }

  const managed_ptr<K>& key() const { return payload; }

  // cppcheck-suppress functionStatic
  bool value() const { return true; }

  // cppcheck-suppress uninitMemberVar
  ManagedTree(TreePtr<K, void>&& left, TreePtr<K, void>&& right,
              payload_type&& payload, Color color)
      : left(std::move(left)),
        right(std::move(right)),
        payload(std::move(payload)),
        color(color) {}

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (left) left.accept(visitor);
    if (right) right.accept(visitor);
    payload.accept(visitor);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedTree);
  }
};

/**
 * Invariants:
 * 1. Red trees have no red children.
 * 2. Black depth of both subtrees is the same.
 * 3. No double-black nodes.
 * 4. Key of left subtree (if present) is less than key.
 * 5. Key is less then key of right subtree (if present).
 */
template <ManagedType K, OptionalManagedType V, typename Comp>
int verify_subtree_invariants(const TreePtr<K, V>& subtree, const Comp& comp) {
  if (!subtree) return 1;
  if (subtree->color == Color::DoubleBlack)
    throw std::logic_error("Double black node in tree.");
  if (subtree->color == Color::Red &&
      ((subtree->left && subtree->left->color == Color::Red) ||
       (subtree->right && subtree->right->color == Color::Red))) {
    throw std::logic_error("Red node has red child.");
  }
  if (subtree->left && !comp(*subtree->left->key(), *subtree->key())) {
    throw std::logic_error("Left subtree's key is not less than key.");
  }
  if (subtree->right && !comp(*subtree->key(), *subtree->right->key())) {
    throw std::logic_error("Key is not less than right subtree's key.");
  }
  int ldepth = verify_subtree_invariants(subtree->left, comp);
  if (ldepth != verify_subtree_invariants(subtree->right, comp)) {
    throw std::logic_error(
        "Left and right subtrees have different black depth.");
  }
  return ldepth + (subtree->color == Color::Black);
}

template <ManagedType K, OptionalManagedType V, typename Comp>
bool verify_invariants(const TreePtr<K, V>& root, const Comp& comp) {
  verify_subtree_invariants(root, comp);
  return true;
}

template <ManagedType K, OptionalManagedType V>
using TreeStack = ConsPtr<ManagedTree<K, V>>;

/**
 * Iterates over a `ManagedTree`.
 *
 * While `tree_iterator` is not a managed type, it both contains
 * references to managed objects and allocates managed objects.
 * Therefore, users of this iterator must at all times make each
 * iterator reachable from a root or else acquire a hold from the
 * memory manager. Incrementing and decrementing this iterator may
 * result in allocations, so a hold must be acquired if you interleave
 * your own allocations with iteration.
 */
template <ManagedType K, OptionalManagedType V, typename Comp>
class tree_iterator {
 public:
  using iterator_concept = std::bidirectional_iterator_tag;
  using difference_type = std::ptrdiff_t;
  using value_type = typename ManagedTree<K, V>::payload_type;
  using reference = const value_type&;
  using pointer = const value_type*;

 public:
  tree_iterator() : stack_(nullptr), comp_(nullptr) {}
  tree_iterator(TreeStack<K, V> stack, const Comp& comp)
      : stack_(std::move(stack)), comp_(&comp) {}
  /** Creates an end iterator for `tree`. */
  tree_iterator(TreePtr<K, V> tree, const Comp& comp)
      : tree_iterator(cons(nullptr, cons(std::move(tree), nullptr)), comp) {}

  reference operator*() const { return stack_->car->payload; }
  pointer operator->() const { return &stack_->car->payload; }

  tree_iterator& operator++() {
    if (stack_->car->right) {
      auto hold = ctx().mgr->acquire_hold();
      stack_ = cons(stack_->car->right, stack_);
      while (stack_->car->left) {
        stack_ = cons(stack_->car->left, stack_);
      }
    } else {
      while (stack_->cdr &&
             (*comp_)(*stack_->cdr->car->key(), *stack_->car->key()))
        stack_ = stack_->cdr;
      if (stack_->cdr) {
        stack_ = stack_->cdr;
      } else {
        // end sentinel -- allows decrementing from end().
        stack_ = cons(nullptr, stack_->cdr);
      }
    }
    return *this;
  }

  tree_iterator operator++(int) {
    auto hold = ctx().mgr->acquire_hold();
    tree_iterator it(*this);
    ++(*this);
    return it;
  }

  tree_iterator& operator--() {
    if (!stack_->car) {
      stack_ = stack_->cdr;
      auto hold = ctx().mgr->acquire_hold();
      while (stack_->car->right) {
        stack_ = cons(stack_->car->right, stack_);
      }
      return *this;
    }
    if (stack_->car->left) {
      auto hold = ctx().mgr->acquire_hold();
      stack_ = cons(stack_->car->left, stack_);
      while (stack_->car->right) {
        stack_ = cons(stack_->car->right, stack_);
      }
      return *this;
    }
    while (stack_->cdr &&
           (*comp_)(*stack_->car->key(), *stack_->cdr->car->key()))
      stack_ = stack_->cdr;
    stack_ = stack_->cdr;
    return *this;
  }

  tree_iterator operator--(int) {
    auto hold = ctx().mgr->acquire_hold();
    tree_iterator it(*this);
    --(*this);
    return it;
  }

  bool operator==(const tree_iterator& o) const {
    return o.stack_->car == stack_->car;
  }

 private:
  TreeStack<K, V> stack_;
  const Comp* comp_;
};

template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find_with_bound(TreePtr<K, V> tree, const U& key,
                                const TreeStack<K, V>& lower_bound,
                                const Comp& comp, TreeStack<K, V> stack) {
  if (!tree) return comp(*lower_bound->car->key(), key) ? nullptr : lower_bound;
  auto new_stack = cons(tree, std::move(stack));
  if (comp(key, *tree->key()))
    return find_with_bound(tree->left, key, lower_bound, comp,
                           std::move(new_stack));
  return find_with_bound(tree->right, key, new_stack, comp, new_stack);
}

template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find_no_bound(TreePtr<K, V> tree, const U& key,
                              const Comp& comp,
                              TreeStack<K, V> stack = nullptr) {
  if (!tree) return nullptr;
  auto new_stack = cons(tree, std::move(stack));
  if (comp(key, *tree->key()))
    return find_no_bound(tree->left, key, comp, std::move(new_stack));
  return find_with_bound(tree->right, key, new_stack, comp, new_stack);
}

/**
 * Find the key in the tree, returning the path from root to the node
 * containing the key. Returns nullptr if not found.
 */
template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find(TreePtr<K, V> tree, const U& key, const Comp& comp) {
  auto hold = ctx().mgr->acquire_hold();
  return find_no_bound(tree, key, comp);
}

/** Balance a red-black tree when inserting in the left-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_ll(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && left && left->left &&
      left->color == Color::Red && left->left->color == Color::Red) {
    return T::make_tree(T::make_tree(left->left->left, left->left->right,
                                     left->left->payload, Color::Black),
                        T::make_tree(left->right, std::move(right),
                                     std::move(payload), Color::Black),
                        left->payload, Color::Red);
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/** Balance a red-black tree when inserting in the left-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_lr(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && left && left->right &&
      left->color == Color::Red && left->right->color == Color::Red) {
    return T::make_tree(T::make_tree(left->left, left->right->left,
                                     left->payload, Color::Black),
                        T::make_tree(left->right->right, std::move(right),
                                     std::move(payload), Color::Black),
                        left->right->payload, Color::Red);
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/** Balance a red-black tree when inserting in the right-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rl(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && right && right->left &&
      right->color == Color::Red && right->left->color == Color::Red) {
    return T::make_tree(T::make_tree(std::move(left), right->left->left,
                                     std::move(payload), Color::Black),
                        T::make_tree(right->left->right, right->right,
                                     right->payload, Color::Black),
                        right->left->payload, Color::Red);
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/** Balance a red-black tree when inserting in the right-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rr(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && right && right->right &&
      right->color == Color::Red && right->right->color == Color::Red) {
    return T::make_tree(T::make_tree(std::move(left), right->left,
                                     std::move(payload), Color::Black),
                        T::make_tree(right->right->left, right->right->right,
                                     right->right->payload, Color::Black),
                        right->payload, Color::Red);
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/**
 * Possibly replace `tree` with a new tree with equivalent payload.
 *
 * Precondition: Payload is equal to tree's payload.
 *
 * If `replace` is true, create a new tree with the new payload.
 */
template <ManagedType K, OptionalManagedType V>
std::optional<TreePtr<K, V>> maybe_replace(
    TreePtr<K, V> tree, typename ManagedTree<K, V>::payload_type&& payload,
    bool replace) {
  if (replace) {
    return ManagedTree<K, V>::make_tree(tree->left, tree->right,
                                        std::move(payload), tree->color);
  }
  return std::nullopt;
}

template <ManagedType K, OptionalManagedType V, typename Comp>
std::optional<TreePtr<K, V>> insert_into_subtree(
    TreePtr<K, V> tree, typename ManagedTree<K, V>::payload_type&& payload,
    const Comp& comp, bool replace) {
  using T = ManagedTree<K, V>;
  if (!tree) {
    return T::make_tree(nullptr, nullptr, std::move(payload), Color::Red);
  }
  const auto& key = T::key(payload);
  if (comp(*key, *tree->key())) {
    const bool not_less_than_left =
        tree->left && !comp(*key, *tree->left->key());
    if (not_less_than_left && !comp(*tree->left->key(), *key)) {
      return maybe_replace(std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(tree->left, std::move(payload), comp, replace)
        .transform([&](managed_ptr<T>&& new_tree) {
          if (!tree->left) {
            return T::make_tree(std::move(new_tree), tree->right, tree->payload,
                                tree->color);
          } else if (not_less_than_left) {
            return balance_lr(tree->color, std::move(new_tree), tree->right,
                              tree->payload);
          } else {
            return balance_ll(tree->color, std::move(new_tree), tree->right,
                              tree->payload);
          }
        });
  } else if (comp(*tree->key(), *key)) {
    const bool not_less_than_right =
        tree->right && !comp(*key, *tree->right->key());
    if (not_less_than_right && !comp(*tree->right->key(), *key)) {
      return maybe_replace(std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(tree->right, std::move(payload), comp, replace)
        .transform([&](auto&& new_tree) {
          if (!tree->right) {
            return T::make_tree(tree->left, std::move(new_tree), tree->payload,
                                tree->color);
          } else if (not_less_than_right) {
            return balance_rr(tree->color, tree->left, std::move(new_tree),
                              tree->payload);
          } else {
            return balance_rl(tree->color, tree->left, std::move(new_tree),
                              tree->payload);
          }
        });
  } else {
    return maybe_replace(std::move(tree), std::move(payload), replace);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> blacken(TreePtr<K, V>&& tree) {
  if (tree && tree->color == Color::Red &&
      ((tree->left && tree->left->color == Color::Red) ||
       (tree->right && tree->right->color == Color::Red))) {
    using T = ManagedTree<K, V>;
    return T::make_tree(tree->left, tree->right, tree->payload, Color::Black);
  } else {
    return tree;
  }
}

/** Insert `payload` into `tree`. */
template <ManagedType K, OptionalManagedType V, typename Comp>
std::pair<TreePtr<K, V>, bool> insert(
    TreePtr<K, V> tree, typename ManagedTree<K, V>::payload_type&& payload,
    const Comp& comp, bool replace) {
  auto hold = ctx().mgr->acquire_hold();
  auto result =
      *insert_into_subtree(tree, std::move(payload), comp, replace)
           .transform([&](auto&& new_tree) {
             return std::make_pair(blacken(std::move(new_tree)), true);
           })
           .or_else([&]() {
             return std::make_optional(std::make_pair(std::move(tree), false));
           });
  return result;
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> undouble(const TreePtr<K, V>& tree) {
  assert(tree && tree->color == Color::DoubleBlack);
  if (!tree->key()) return nullptr;
  using T = ManagedTree<K, V>;
  return T::make_tree(tree->left, tree->right, tree->payload, Color::Black);
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_bbl(TreePtr<K, V> ll, TreePtr<K, V> lr,
                          typename ManagedTree<K, V>::payload_type left,
                          TreePtr<K, V> right,
                          typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (lr && lr->color == Color::Red) {
    return T::make_tree(
        T::make_tree(std::move(ll), lr->left, std::move(left), Color::Black),
        T::make_tree(lr->right, std::move(right), std::move(payload),
                     Color::Black),
        lr->payload, Color::Black);
  } else {
    return T::make_tree(
        T::make_tree(std::move(ll), std::move(lr), std::move(left), Color::Red),
        std::move(right), std::move(payload), Color::DoubleBlack);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_bbr(TreePtr<K, V> left, TreePtr<K, V> rl,
                          TreePtr<K, V> rr,
                          typename ManagedTree<K, V>::payload_type right,
                          typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (rl && rl->color == Color::Red) {
    return T::make_tree(
        T::make_tree(std::move(left), rl->left, std::move(payload),
                     Color::Black),
        T::make_tree(rl->right, std::move(rr), std::move(right), Color::Black),
        rl->payload, Color::Black);
  } else {
    return T::make_tree(std::move(left),
                        T::make_tree(std::move(rl), std::move(rr),
                                     std::move(right), Color::Red),
                        std::move(payload), Color::DoubleBlack);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> rotate_l(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                       typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  assert(color != Color::DoubleBlack);
  if (left && left->color == Color::DoubleBlack) {
    assert(right);
    if (color == Color::Red) {
      if (right->color == Color::Black) {
        return balance_lr(Color::Black,
                          T::make_tree(undouble(left), right->left,
                                       std::move(payload), Color::Red),
                          right->right, right->payload);
      }
    } else if (right->color == Color::Black) {
      return balance_bbl(undouble(left), right->left, std::move(payload),
                         right->right, right->payload);
    } else if (right->left && right->left->color == Color::Black) {
      auto new_left = balance_lr(Color::Black,
                                 T::make_tree(undouble(left), right->left->left,
                                              std::move(payload), Color::Red),
                                 right->left->right, right->left->payload);
      return T::make_tree(std::move(new_left), right->right, right->payload,
                          Color::Black);
    }
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> rotate_r(Color color, TreePtr<K, V> left, TreePtr<K, V> right,
                       typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  assert(color != Color::DoubleBlack);
  if (right && right->color == Color::DoubleBlack) {
    assert(left);
    if (color == Color::Red) {
      if (left->color == Color::Black) {
        return balance_rl(Color::Black, left->left,
                          T::make_tree(left->right, undouble(right),
                                       std::move(payload), Color::Red),
                          left->payload);
      }
    } else if (left->color == Color::Black) {
      return balance_bbr(left->left, left->right, undouble(right),
                         std::move(payload), left->payload);
    } else if (left->right && left->right->color == Color::Black) {
      auto new_right =
          balance_rl(Color::Black, left->right->left,
                     T::make_tree(left->right->right, undouble(right),
                                  std::move(payload), Color::Red),
                     left->right->payload);
      return T::make_tree(left->left, std::move(new_right), left->payload,
                          Color::Black);
    }
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/** Delete the smallest element in `tree` (ie its leftmost node). */
template <ManagedType K, OptionalManagedType V>
std::pair<TreePtr<K, V>, typename ManagedTree<K, V>::payload_type> erase_min(
    TreePtr<K, V> tree) {
  using T = ManagedTree<K, V>;
  if (!tree) throw std::logic_error("Deleting min from empty tree.");
  if (tree->color == Color::Red && !tree->left && !tree->right) {
    return std::make_pair(nullptr, tree->payload);
  } else if (tree->color == Color::Black && !tree->left) {
    if (!tree->right) {
      return std::make_pair(T::double_black_empty(), tree->payload);
    } else if (tree->right->color == Color::Red) {
      return std::make_pair(T::make_tree(tree->right->left, tree->right->right,
                                         tree->right->payload, Color::Black),
                            tree->payload);
    }
  }
  auto [left, payload] = erase_min(tree->left);
  return std::make_pair(
      rotate_l(tree->color, std::move(left), tree->right, tree->payload),
      std::move(payload));
}

/** Delete `key` from `tree`. */
template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
std::optional<std::pair<TreePtr<K, V>, typename ManagedTree<K, V>::value_type>>
erase_from_subtree(TreePtr<K, V> tree, const U& key, const Comp& comp) {
  using T = ManagedTree<K, V>;
  if (!tree) {
    return std::nullopt;
  }
  if (comp(key, *tree->key())) {
    return erase_from_subtree(tree->left, key, comp)
        .transform([&](auto&& result) {
          return std::make_pair(rotate_l(tree->color, std::move(result.first),
                                         tree->right, tree->payload),
                                std::move(result.second));
        });
  } else if (comp(*tree->key(), key)) {
    return erase_from_subtree(tree->right, key, comp)
        .transform([&](auto&& result) {
          return std::make_pair(
              rotate_r(tree->color, tree->left, std::move(result.first),
                       tree->payload),
              std::move(result.second));
        });
  } else if (tree->color == Color::Red && !tree->left && !tree->right) {
    return std::make_pair(nullptr, tree->value());
  } else if (tree->color == Color::Black && !tree->right) {
    if (!tree->left) {
      return std::make_pair(T::double_black_empty(), tree->value());
    } else if (tree->left->color == Color::Red) {
      return std::make_pair(T::make_tree(tree->left->left, tree->left->right,
                                         tree->left->payload, Color::Black),
                            tree->value());
    }
  }
  auto [right, payload] = erase_min(tree->right);
  return std::make_pair(
      rotate_r(tree->color, tree->left, std::move(right), std::move(payload)),
      tree->value());
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> redden(TreePtr<K, V>&& tree) {
  if (tree && tree->color == Color::Black &&
      (!tree->left || tree->left->color == Color::Black) &&
      (!tree->right || tree->right->color == Color::Black)) {
    using T = ManagedTree<K, V>;
    return T::make_tree(tree->left, tree->right, tree->payload, Color::Red);
  } else {
    return tree;
  }
}

/**
 * Delete `key` from `tree`.
 *
 * Returns the new tree and either a flag indicating whether the `key`
 * was present before erasure (for V=void) or the previously mapped
 * value for `key` (for V!=void).
 */
template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
std::pair<TreePtr<K, V>, typename ManagedTree<K, V>::maybe_value_type> erase(
    TreePtr<K, V> tree, const U& key, const Comp& comp) {
  using T = ManagedTree<K, V>;
  auto hold = ctx().mgr->acquire_hold();
  auto result =
      *erase_from_subtree(redden(std::move(tree)), key, comp)
           .transform([&](auto&& result) {
             return std::make_pair(std::move(result.first),
                                   T::maybe_value(std::move(result.second)));
           })
           .or_else([&]() {
             return std::make_optional(
                 std::make_pair(std::move(tree), T::no_value()));
           });
  return result;
}

}  // namespace detail

namespace testing {
class ManagedMapAccessor;
class ManagedSetAccessor;
}  // namespace testing

/**
 * A set of managed values, with O(lg n) insertion and deletion times.
 *
 * This set is immutable and *persistent* in the sense described in
 * https://en.wikipedia.org/wiki/Persistent_data_structure.
 *
 * See comments about `detail::tree_iterator`'s interaction with the
 * memory manager.
 */
template <ManagedType T, typename Comp = std::less<>>
class ManagedSet : public ManagedWithSelfPtr<ManagedSet<T, Comp>> {
  struct token {
   private:
    token() {}
    friend ManagedSet;
  };

 public:
  using iterator = detail::tree_iterator<T, void, Comp>;
  using const_iterator = iterator;
  using reverse_iterator = std::reverse_iterator<iterator>;
  using const_reverse_iterator = std::reverse_iterator<const_iterator>;
  using value_type = typename iterator::value_type;

  static_assert(std::bidirectional_iterator<iterator>);

  ManagedSet() : ManagedSet(Comp()) {}
  explicit ManagedSet(const Comp& comp)
      : ManagedSet(token{}, comp, nullptr, 0) {}
  /** Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134. */
  ManagedSet(token, const Comp& comp, detail::TreePtr<T> tree, std::size_t size)
      : comp_(&comp), tree_(std::move(tree)), size_(size) {}

  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const {
    auto hold = ctx().mgr->acquire_hold();
    if (!tree_) return {tree_, *comp_};
    auto stack = cons(tree_, nullptr);
    while (stack->car->left) {
      stack = cons(stack->car->left, std::move(stack));
    }
    return {std::move(stack), *comp_};
  }

  iterator end() const { return cend(); }
  const_iterator cend() const { return {tree_, *comp_}; }

  reverse_iterator rbegin() const { return crbegin(); }
  const_reverse_iterator crbegin() const {
    return const_reverse_iterator(cend());
  }

  reverse_iterator rend() const { return crend(); }
  const_reverse_iterator crend() const {
    return const_reverse_iterator(cbegin());
  }

  bool empty() const noexcept { return !tree_; }
  std::size_t size() const noexcept { return size_; }

  template <typename U>
  const_iterator find(const U& needle) const {
    auto s = detail::find(tree_, needle, *comp_);
    return s ? const_iterator(std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& needle) const {
    return static_cast<bool>(detail::find(tree_, needle, *comp_));
  }

  /**
   * Insert `t` into this set.
   *
   * Returns the resulting set and a flag that is true if the
   * resulting set is different than the current set (i.e. if `t` was
   * not already in this set.)
   *
   * `t` must be reachable or this must be called under a hold.
   */
  std::pair<managed_ptr<ManagedSet<T, Comp>>, bool> insert(
      managed_ptr<T> t) const {
    auto result = detail::insert(tree_, std::move(t), *comp_, false);
    if (result.second) {
      return std::make_pair(
          make_managed<ManagedSet<T, Comp>>(token{}, *comp_,
                                            std::move(result.first), size_ + 1),
          true);
    } else {
      return std::make_pair(this->self(), false);
    }
  }

  template <typename... Args>
  std::pair<managed_ptr<ManagedSet<T, Comp>>, bool> emplace(Args&&... args) {
    auto hold = ctx().mgr->acquire_hold();
    return insert(make_managed<T>(std::forward<Args>(args)...));
  }

  /**
   * Remove `val` from this set.
   *
   * Returns the resulting set and a flag that is true if the resulting set is
   * different than the current set (i.e. if `t` was already in this set).
   */
  template <typename U>
  std::pair<managed_ptr<ManagedSet<T, Comp>>, bool> erase(const U& val) const {
    auto hold = ctx().mgr->acquire_hold();
    auto result = detail::erase(tree_, val, *comp_);
    if (result.second) {
      return std::make_pair(
          make_managed<ManagedSet<T, Comp>>(token{}, *comp_,
                                            std::move(result.first), size_ - 1),
          true);
    } else {
      return std::make_pair(this->self(), false);
    }
  }

 private:
  friend class MemoryManager;
  friend class testing::ManagedSetAccessor;

  const Comp* comp_;
  detail::TreePtr<T> tree_;
  std::size_t size_ = 0;

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (tree_) tree_.accept(visitor);
    if constexpr (ManagedType<Comp>) {
      comp_->accept(visitor);
    }
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedSet);
  }
};

template <ManagedType T, typename Comp = std::less<>>
using SetPtr = managed_ptr<ManagedSet<T, Comp>>;

/**
 * Creates a `ManagedSet` with the given elements.
 *
 * All elements must be reachable or else this must be called with a hold.
 */
template <ManagedType T, typename Comp>
SetPtr<T, Comp> managed_set(const Comp& comp,
                            std::initializer_list<managed_ptr<T>> els) {
  auto hold = ctx().mgr->acquire_hold();
  auto s = make_managed<ManagedSet<T, Comp>>(comp);
  for (const auto& el : els) {
    s = s->insert(el).first;
  }
  return s;
}

/** @overload */
template <ManagedType T>
SetPtr<T> managed_set(std::initializer_list<managed_ptr<T>> els) {
  return managed_set(std::less<>(), els);
}

/**
 * A map whose keys and values are managed, with O(lg n) insertion and deletion
 * times.
 *
 * This map is immutable and *persistent* in the sense described in
 * https://en.wikipedia.org/wiki/Persistent_data_structure.
 *
 * See comments about `detail::tree_iterator`'s interaction with the memory
 * manager.
 */
template <ManagedType K, ManagedType V, typename Comp = std::less<>>
class ManagedMap : public ManagedWithSelfPtr<ManagedMap<K, V, Comp>> {
  struct token {
   private:
    token() {}
    friend ManagedMap;
  };

 public:
  using iterator = detail::tree_iterator<K, V, Comp>;
  using const_iterator = iterator;
  using reverse_iterator = std::reverse_iterator<iterator>;
  using const_reverse_iterator = std::reverse_iterator<const_iterator>;
  using value_type = typename iterator::value_type;

  static_assert(std::bidirectional_iterator<iterator>);

  ManagedMap() : ManagedMap(Comp()) {}
  explicit ManagedMap(const Comp& comp)
      : ManagedMap(token{}, comp, nullptr, 0) {}
  /** Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134. */
  ManagedMap(token, const Comp& comp, detail::TreePtr<K, V> tree,
             std::size_t size)
      : comp_(&comp), tree_(std::move(tree)), size_(size) {}
  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const {
    auto hold = ctx().mgr->acquire_hold();
    if (!tree_) return {tree_, *comp_};
    auto stack = cons(tree_, nullptr);
    while (stack->car->left) {
      stack = cons(stack->car->left, std::move(stack));
    }
    return {std::move(stack), *comp_};
  }

  iterator end() const { return cend(); }
  const_iterator cend() const { return {tree_, *comp_}; }

  reverse_iterator rbegin() const { return crbegin(); }
  const_reverse_iterator crbegin() const {
    return const_reverse_iterator(cend());
  }

  reverse_iterator rend() const { return crend(); }
  const_reverse_iterator crend() const {
    return const_reverse_iterator(cbegin());
  }

  bool empty() const noexcept { return !tree_; }
  std::size_t size() const noexcept { return size_; }

  template <typename U>
  const_iterator find(const U& key) const {
    auto s = detail::find(tree_, key, *comp_);
    return s ? const_iterator(std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& key) const {
    return static_cast<bool>(detail::find(tree_, key, *comp_));
  }

  template <typename U>
  std::optional<managed_ptr<V>> get(const U& key) const {
    auto s = detail::find(tree_, key, *comp_);
    return s ? std::make_optional(s->car->value()) : std::nullopt;
  }

  /**
   * Insert a mapping from `k` to `v` into this map, replacing any existing
   * mapping from `k`.
   *
   * Returns the resulting map and the previous value, if any.
   *
   * `k` and `v` must be reachable or this must be called under a hold.
   */
  std::pair<managed_ptr<ManagedMap<K, V, Comp>>, std::optional<managed_ptr<V>>>
  insert(managed_ptr<K> k, managed_ptr<V> v) const {
    auto hold = ctx().mgr->acquire_hold();
    auto stack = detail::find(tree_, *k, *comp_);
    if (stack) {
      using T = detail::ManagedTree<K, V>;
      assert(!(*comp_)(*k, *stack->car->key()) &&
             !(*comp_)(*stack->car->key(), *k));
      auto old_value = std::make_optional(stack->car->value());
      detail::TreePtr<K, V> new_tree = T::make_tree(
          stack->car->left, stack->car->right,
          std::make_pair(std::move(k), std::move(v)), stack->car->color);
      while (stack->cdr) {
        stack = stack->cdr;
        const bool is_left = (*comp_)(*new_tree->key(), *stack->car->key());
        new_tree =
            T::make_tree(is_left ? std::move(new_tree) : stack->car->left,
                         is_left ? stack->car->right : std::move(new_tree),
                         stack->car->payload, stack->car->color);
      }
      return std::make_pair(make_managed<ManagedMap<K, V, Comp>>(
                                token{}, *comp_, std::move(new_tree), size_),
                            std::move(old_value));
    }
    auto result = detail::insert(
        tree_, std::make_pair(std::move(k), std::move(v)), *comp_, true);
    assert(result.second);
    return std::make_pair(
        make_managed<ManagedMap<K, V, Comp>>(
            token{}, *comp_, std::move(result.first), size_ + 1),
        std::nullopt);
  }

  template <typename KTuple, typename VTuple>
  std::pair<managed_ptr<ManagedMap<K, V, Comp>>, std::optional<managed_ptr<V>>>
  emplace(KTuple&& kargs, VTuple&& vargs) const {
    auto hold = ctx().mgr->acquire_hold();
    return insert(
        std::apply(
            [&](auto&&... args) {
              return make_managed<K>(std::forward<decltype(args)>(args)...);
            },
            std::forward<KTuple>(kargs)),
        std::apply(
            [&](auto&&... args) {
              return make_managed<V>(std::forward<decltype(args)>(args)...);
            },
            std::forward<VTuple>(vargs)));
  }

  /**
   * Remove `key` from this map.
   *
   * Returns the resulting map and the previous value `key` was mapped to, if
   * any.
   */
  template <typename U>
  std::pair<managed_ptr<ManagedMap<K, V, Comp>>, std::optional<managed_ptr<V>>>
  erase(const U& key) const {
    auto hold = ctx().mgr->acquire_hold();
    auto result = detail::erase(tree_, key, *comp_);
    if (result.second) {
      return std::make_pair(
          make_managed<ManagedMap<K, V, Comp>>(
              token{}, *comp_, std::move(result.first), size_ - 1),
          std::move(result.second));
    } else {
      return std::make_pair(this->self(), std::nullopt);
    }
  }

 private:
  friend class testing::ManagedMapAccessor;

  const Comp* comp_;
  detail::TreePtr<K, V> tree_;
  std::size_t size_;

  void visit_subobjects(const ManagedVisitor& visitor) override {
    if (tree_) tree_.accept(visitor);
    if constexpr (ManagedType<Comp>) {
      comp_->accept(visitor);
    }
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedMap);
  }
};

template <ManagedType K, ManagedType V, typename Comp = std::less<>>
using MapPtr = managed_ptr<ManagedMap<K, V, Comp>>;

/**
 * Creates a `ManagedMap` with the given elements.
 *
 * All elements must be reachable or else this must be called with a hold.
 */
template <ManagedType K, ManagedType V, typename Comp>
MapPtr<K, V, Comp> managed_map(
    const Comp& comp,
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els) {
  auto hold = ctx().mgr->acquire_hold();
  auto m = make_managed<ManagedMap<K, V, Comp>>(comp);
  for (const auto& el : els) {
    m = m->insert(el.first, el.second).first;
  }
  return m;
}

/** @overload */
template <ManagedType K, ManagedType V>
MapPtr<K, V> managed_map(
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els) {
  return managed_map(std::less<>(), els);
}
}  // namespace emil::collections
