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

#include <cassert>
#include <cstddef>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <optional>
#include <stdexcept>
#include <utility>

#include "emil/gc.h"

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
ConsPtr<T> cons(MemoryManager& mgr, managed_ptr<T> car, ConsPtr<T> cdr) {
  return mgr.create<ManagedCons<T>>(std::move(car), std::move(cdr));
}

/** @overload */
template <ManagedType T>
ConsPtr<T> cons(MemoryManager& mgr, managed_ptr<T> car, std::nullptr_t) {
  return mgr.create<ManagedCons<T>>(std::move(car), nullptr);
}

/** @overload */
template <ManagedType T>
ConsPtr<T> cons(MemoryManager& mgr, std::nullptr_t, ConsPtr<T> cdr) {
  return mgr.create<ManagedCons<T>>(nullptr, std::move(cdr));
}

/**
 * Construct and prepend a `T` to `cdr`.
 */
template <ManagedType T, typename... Args>
ConsPtr<T> cons_in_place(MemoryManager& mgr, ConsPtr<T> cdr, Args&&... args) {
  auto hold = mgr.acquire_hold();
  // cppcheck-suppress redundantInitialization
  auto car = mgr.create<T>(std::forward<Args>(args)...);
  return mgr.create<ManagedCons<T>>(std::move(car), std::move(cdr));
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

  static TreePtr<K, V> make_tree(MemoryManager& mgr, TreePtr<K, V> left,
                                 TreePtr<K, V> right, payload_type payload,
                                 Color color) {
    return mgr.create<ManagedTree<K, V>>(std::move(left), std::move(right),
                                         std::move(payload), color);
  }

  static const managed_ptr<K>& key(const payload_type& payload) {
    return payload.first;
  }

  static maybe_value_type maybe_value(value_type&& v) {
    return std::make_optional(std::move(v));
  }

  static maybe_value_type no_value() { return std::nullopt; }

  static TreePtr<K, V> double_black_empty(MemoryManager& mgr) {
    return make_tree(mgr, nullptr, nullptr, {nullptr, nullptr},
                     Color::DoubleBlack);
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

  static TreePtr<K> make_tree(MemoryManager& mgr, TreePtr<K> left,
                              TreePtr<K> right, payload_type payload,
                              Color color) {
    return mgr.create<ManagedTree<K>>(std::move(left), std::move(right),
                                      std::move(payload), color);
  }

  static const managed_ptr<K>& key(const payload_type& payload) {
    return payload;
  }

  static bool maybe_value(bool v) { return v; }
  static bool no_value() { return false; }

  static TreePtr<K> double_black_empty(MemoryManager& mgr) {
    return make_tree(mgr, nullptr, nullptr, nullptr, Color::DoubleBlack);
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
  tree_iterator() : mgr_(nullptr), stack_(nullptr), comp_(nullptr) {}
  tree_iterator(MemoryManager& mgr, TreeStack<K, V> stack, const Comp& comp)
      : mgr_(&mgr), stack_(std::move(stack)), comp_(&comp) {}
  /** Creates an end iterator for `tree`. */
  tree_iterator(MemoryManager& mgr, TreePtr<K, V> tree, const Comp& comp)
      : tree_iterator(mgr,
                      cons(mgr, nullptr, cons(mgr, std::move(tree), nullptr)),
                      comp) {}

  reference operator*() const { return stack_->car->payload; }
  pointer operator->() const { return &stack_->car->payload; }

  tree_iterator& operator++() {
    if (stack_->car->right) {
      auto hold = mgr_->acquire_hold();
      stack_ = cons(*mgr_, stack_->car->right, stack_);
      while (stack_->car->left) {
        stack_ = cons(*mgr_, stack_->car->left, stack_);
      }
    } else {
      while (stack_->cdr &&
             (*comp_)(*stack_->cdr->car->key(), *stack_->car->key()))
        stack_ = stack_->cdr;
      if (stack_->cdr) {
        stack_ = stack_->cdr;
      } else {
        // end sentinel -- allows decrementing from end().
        stack_ = cons(*mgr_, nullptr, stack_->cdr);
      }
    }
    return *this;
  }

  tree_iterator operator++(int) {
    auto hold = mgr_->acquire_hold();
    tree_iterator it(*this);
    ++(*this);
    return it;
  }

  tree_iterator& operator--() {
    if (!stack_->car) {
      stack_ = stack_->cdr;
      auto hold = mgr_->acquire_hold();
      while (stack_->car->right) {
        stack_ = cons(*mgr_, stack_->car->right, stack_);
      }
      return *this;
    }
    if (stack_->car->left) {
      auto hold = mgr_->acquire_hold();
      stack_ = cons(*mgr_, stack_->car->left, stack_);
      while (stack_->car->right) {
        stack_ = cons(*mgr_, stack_->car->right, stack_);
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
    auto hold = mgr_->acquire_hold();
    tree_iterator it(*this);
    --(*this);
    return it;
  }

  bool operator==(const tree_iterator& o) const {
    return o.stack_->car == stack_->car;
  }

 private:
  MemoryManager* mgr_;
  TreeStack<K, V> stack_;
  const Comp* comp_;
};

template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find_with_bound(MemoryManager& mgr, TreePtr<K, V> tree,
                                const U& key,
                                const TreeStack<K, V>& lower_bound,
                                const Comp& comp, TreeStack<K, V> stack) {
  if (!tree) return comp(*lower_bound->car->key(), key) ? nullptr : lower_bound;
  auto new_stack = cons(mgr, tree, std::move(stack));
  if (comp(key, *tree->key()))
    return find_with_bound(mgr, tree->left, key, lower_bound, comp,
                           std::move(new_stack));
  return find_with_bound(mgr, tree->right, key, new_stack, comp, new_stack);
}

template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find_no_bound(MemoryManager& mgr, TreePtr<K, V> tree,
                              const U& key, const Comp& comp,
                              TreeStack<K, V> stack = nullptr) {
  if (!tree) return nullptr;
  auto new_stack = cons(mgr, tree, std::move(stack));
  if (comp(key, *tree->key()))
    return find_no_bound(mgr, tree->left, key, comp, std::move(new_stack));
  return find_with_bound(mgr, tree->right, key, new_stack, comp, new_stack);
}

/**
 * Find the key in the tree, returning the path from root to the node
 * containing the key. Returns nullptr if not found.
 */
template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find(MemoryManager& mgr, TreePtr<K, V> tree, const U& key,
                     const Comp& comp) {
  auto hold = mgr.acquire_hold();
  return find_no_bound(mgr, tree, key, comp);
}

/** Balance a red-black tree when inserting in the left-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_ll(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && left && left->left &&
      left->color == Color::Red && left->left->color == Color::Red) {
    return T::make_tree(mgr,
                        T::make_tree(mgr, left->left->left, left->left->right,
                                     left->left->payload, Color::Black),
                        T::make_tree(mgr, left->right, std::move(right),
                                     std::move(payload), Color::Black),
                        left->payload, Color::Red);
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the left-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_lr(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && left && left->right &&
      left->color == Color::Red && left->right->color == Color::Red) {
    return T::make_tree(mgr,
                        T::make_tree(mgr, left->left, left->right->left,
                                     left->payload, Color::Black),
                        T::make_tree(mgr, left->right->right, std::move(right),
                                     std::move(payload), Color::Black),
                        left->right->payload, Color::Red);
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the right-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rl(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && right && right->left &&
      right->color == Color::Red && right->left->color == Color::Red) {
    return T::make_tree(mgr,
                        T::make_tree(mgr, std::move(left), right->left->left,
                                     std::move(payload), Color::Black),
                        T::make_tree(mgr, right->left->right, right->right,
                                     right->payload, Color::Black),
                        right->left->payload, Color::Red);
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the right-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rr(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (color == Color::Black && right && right->right &&
      right->color == Color::Red && right->right->color == Color::Red) {
    return T::make_tree(
        mgr,
        T::make_tree(mgr, std::move(left), right->left, std::move(payload),
                     Color::Black),
        T::make_tree(mgr, right->right->left, right->right->right,
                     right->right->payload, Color::Black),
        right->payload, Color::Red);
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
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
    MemoryManager& mgr, TreePtr<K, V> tree,
    typename ManagedTree<K, V>::payload_type&& payload, bool replace) {
  if (replace) {
    return ManagedTree<K, V>::make_tree(mgr, tree->left, tree->right,
                                        std::move(payload), tree->color);
  }
  return std::nullopt;
}

template <ManagedType K, OptionalManagedType V, typename Comp>
std::optional<TreePtr<K, V>> insert_into_subtree(
    MemoryManager& mgr, TreePtr<K, V> tree,
    typename ManagedTree<K, V>::payload_type&& payload, const Comp& comp,
    bool replace) {
  using T = ManagedTree<K, V>;
  if (!tree) {
    return T::make_tree(mgr, nullptr, nullptr, std::move(payload), Color::Red);
  }
  const auto& key = T::key(payload);
  if (comp(*key, *tree->key())) {
    const bool not_less_than_left =
        tree->left && !comp(*key, *tree->left->key());
    if (not_less_than_left && !comp(*tree->left->key(), *key)) {
      return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(mgr, tree->left, std::move(payload), comp,
                               replace)
        .transform([&](managed_ptr<T>&& new_tree) {
          if (!tree->left) {
            return T::make_tree(mgr, std::move(new_tree), tree->right,
                                tree->payload, tree->color);
          } else if (not_less_than_left) {
            return balance_lr(mgr, tree->color, std::move(new_tree),
                              tree->right, tree->payload);
          } else {
            return balance_ll(mgr, tree->color, std::move(new_tree),
                              tree->right, tree->payload);
          }
        });
  } else if (comp(*tree->key(), *key)) {
    const bool not_less_than_right =
        tree->right && !comp(*key, *tree->right->key());
    if (not_less_than_right && !comp(*tree->right->key(), *key)) {
      return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(mgr, tree->right, std::move(payload), comp,
                               replace)
        .transform([&](auto&& new_tree) {
          if (!tree->right) {
            return T::make_tree(mgr, tree->left, std::move(new_tree),
                                tree->payload, tree->color);
          } else if (not_less_than_right) {
            return balance_rr(mgr, tree->color, tree->left, std::move(new_tree),
                              tree->payload);
          } else {
            return balance_rl(mgr, tree->color, tree->left, std::move(new_tree),
                              tree->payload);
          }
        });
  } else {
    return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> blacken(MemoryManager& mgr, TreePtr<K, V>&& tree) {
  if (tree && tree->color == Color::Red &&
      ((tree->left && tree->left->color == Color::Red) ||
       (tree->right && tree->right->color == Color::Red))) {
    using T = ManagedTree<K, V>;
    return T::make_tree(mgr, tree->left, tree->right, tree->payload,
                        Color::Black);
  } else {
    return tree;
  }
}

/** Insert `payload` into `tree`. */
template <ManagedType K, OptionalManagedType V, typename Comp>
std::pair<TreePtr<K, V>, bool> insert(
    MemoryManager& mgr, TreePtr<K, V> tree,
    typename ManagedTree<K, V>::payload_type&& payload, const Comp& comp,
    bool replace) {
  auto hold = mgr.acquire_hold();
  auto result =
      *insert_into_subtree(mgr, tree, std::move(payload), comp, replace)
           .transform([&](auto&& new_tree) {
             return std::make_pair(blacken(mgr, std::move(new_tree)), true);
           })
           .or_else([&]() {
             return std::make_optional(std::make_pair(std::move(tree), false));
           });
  return result;
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> undouble(MemoryManager& mgr, const TreePtr<K, V>& tree) {
  assert(tree && tree->color == Color::DoubleBlack);
  if (!tree->key()) return nullptr;
  using T = ManagedTree<K, V>;
  return T::make_tree(mgr, tree->left, tree->right, tree->payload,
                      Color::Black);
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_bbl(MemoryManager& mgr, TreePtr<K, V> ll,
                          TreePtr<K, V> lr,
                          typename ManagedTree<K, V>::payload_type left,
                          TreePtr<K, V> right,
                          typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (lr && lr->color == Color::Red) {
    return T::make_tree(mgr,
                        T::make_tree(mgr, std::move(ll), lr->left,
                                     std::move(left), Color::Black),
                        T::make_tree(mgr, lr->right, std::move(right),
                                     std::move(payload), Color::Black),
                        lr->payload, Color::Black);
  } else {
    return T::make_tree(mgr,
                        T::make_tree(mgr, std::move(ll), std::move(lr),
                                     std::move(left), Color::Red),
                        std::move(right), std::move(payload),
                        Color::DoubleBlack);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_bbr(MemoryManager& mgr, TreePtr<K, V> left,
                          TreePtr<K, V> rl, TreePtr<K, V> rr,
                          typename ManagedTree<K, V>::payload_type right,
                          typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  if (rl && rl->color == Color::Red) {
    return T::make_tree(mgr,
                        T::make_tree(mgr, std::move(left), rl->left,
                                     std::move(payload), Color::Black),
                        T::make_tree(mgr, rl->right, std::move(rr),
                                     std::move(right), Color::Black),
                        rl->payload, Color::Black);
  } else {
    return T::make_tree(mgr, std::move(left),
                        T::make_tree(mgr, std::move(rl), std::move(rr),
                                     std::move(right), Color::Red),
                        std::move(payload), Color::DoubleBlack);
  }
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> rotate_l(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                       TreePtr<K, V> right,
                       typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  assert(color != Color::DoubleBlack);
  if (left && left->color == Color::DoubleBlack) {
    assert(right);
    if (color == Color::Red) {
      if (right->color == Color::Black) {
        return balance_lr(mgr, Color::Black,
                          T::make_tree(mgr, undouble(mgr, left), right->left,
                                       std::move(payload), Color::Red),
                          right->right, right->payload);
      }
    } else if (right->color == Color::Black) {
      return balance_bbl(mgr, undouble(mgr, left), right->left,
                         std::move(payload), right->right, right->payload);
    } else if (right->left && right->left->color == Color::Black) {
      auto new_left =
          balance_lr(mgr, Color::Black,
                     T::make_tree(mgr, undouble(mgr, left), right->left->left,
                                  std::move(payload), Color::Red),
                     right->left->right, right->left->payload);
      return T::make_tree(mgr, std::move(new_left), right->right,
                          right->payload, Color::Black);
    }
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> rotate_r(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                       TreePtr<K, V> right,
                       typename ManagedTree<K, V>::payload_type payload) {
  using T = ManagedTree<K, V>;
  assert(color != Color::DoubleBlack);
  if (right && right->color == Color::DoubleBlack) {
    assert(left);
    if (color == Color::Red) {
      if (left->color == Color::Black) {
        return balance_rl(mgr, Color::Black, left->left,
                          T::make_tree(mgr, left->right, undouble(mgr, right),
                                       std::move(payload), Color::Red),
                          left->payload);
      }
    } else if (left->color == Color::Black) {
      return balance_bbr(mgr, left->left, left->right, undouble(mgr, right),
                         std::move(payload), left->payload);
    } else if (left->right && left->right->color == Color::Black) {
      auto new_right =
          balance_rl(mgr, Color::Black, left->right->left,
                     T::make_tree(mgr, left->right->right, undouble(mgr, right),
                                  std::move(payload), Color::Red),
                     left->right->payload);
      return T::make_tree(mgr, left->left, std::move(new_right), left->payload,
                          Color::Black);
    }
  }
  return T::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Delete the smallest element in `tree` (ie its leftmost node). */
template <ManagedType K, OptionalManagedType V>
std::pair<TreePtr<K, V>, typename ManagedTree<K, V>::payload_type> erase_min(
    MemoryManager& mgr, TreePtr<K, V> tree) {
  using T = ManagedTree<K, V>;
  if (!tree) throw std::logic_error("Deleting min from empty tree.");
  if (tree->color == Color::Red && !tree->left && !tree->right) {
    return std::make_pair(nullptr, tree->payload);
  } else if (tree->color == Color::Black && !tree->left) {
    if (!tree->right) {
      return std::make_pair(T::double_black_empty(mgr), tree->payload);
    } else if (tree->right->color == Color::Red) {
      return std::make_pair(
          T::make_tree(mgr, tree->right->left, tree->right->right,
                       tree->right->payload, Color::Black),
          tree->payload);
    }
  }
  auto [left, payload] = erase_min(mgr, tree->left);
  return std::make_pair(
      rotate_l(mgr, tree->color, std::move(left), tree->right, tree->payload),
      std::move(payload));
}

/** Delete `key` from `tree`. */
template <typename U, ManagedType K, OptionalManagedType V, typename Comp>
std::optional<std::pair<TreePtr<K, V>, typename ManagedTree<K, V>::value_type>>
erase_from_subtree(MemoryManager& mgr, TreePtr<K, V> tree, const U& key,
                   const Comp& comp) {
  using T = ManagedTree<K, V>;
  if (!tree) {
    return std::nullopt;
  }
  if (comp(key, *tree->key())) {
    return erase_from_subtree(mgr, tree->left, key, comp)
        .transform([&](auto&& result) {
          return std::make_pair(
              rotate_l(mgr, tree->color, std::move(result.first), tree->right,
                       tree->payload),
              std::move(result.second));
        });
  } else if (comp(*tree->key(), key)) {
    return erase_from_subtree(mgr, tree->right, key, comp)
        .transform([&](auto&& result) {
          return std::make_pair(
              rotate_r(mgr, tree->color, tree->left, std::move(result.first),
                       tree->payload),
              std::move(result.second));
        });
  } else if (tree->color == Color::Red && !tree->left && !tree->right) {
    return std::make_pair(nullptr, tree->value());
  } else if (tree->color == Color::Black && !tree->right) {
    if (!tree->left) {
      return std::make_pair(T::double_black_empty(mgr), tree->value());
    } else if (tree->left->color == Color::Red) {
      return std::make_pair(
          T::make_tree(mgr, tree->left->left, tree->left->right,
                       tree->left->payload, Color::Black),
          tree->value());
    }
  }
  auto [right, payload] = erase_min(mgr, tree->right);
  return std::make_pair(rotate_r(mgr, tree->color, tree->left, std::move(right),
                                 std::move(payload)),
                        tree->value());
}

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> redden(MemoryManager& mgr, TreePtr<K, V>&& tree) {
  if (tree && tree->color == Color::Black &&
      (!tree->left || tree->left->color == Color::Black) &&
      (!tree->right || tree->right->color == Color::Black)) {
    using T = ManagedTree<K, V>;
    return T::make_tree(mgr, tree->left, tree->right, tree->payload,
                        Color::Red);
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
    MemoryManager& mgr, TreePtr<K, V> tree, const U& key, const Comp& comp) {
  using T = ManagedTree<K, V>;
  auto hold = mgr.acquire_hold();
  auto result =
      *erase_from_subtree(mgr, redden(mgr, std::move(tree)), key, comp)
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
template <ManagedType T, typename Comp = std::less<T>>
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

  explicit ManagedSet(MemoryManager& mgr) : ManagedSet(mgr, Comp()) {}
  ManagedSet(MemoryManager& mgr, const Comp& comp)
      : ManagedSet(token{}, mgr, comp, nullptr, 0) {}
  /** Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134. */
  ManagedSet(token, MemoryManager& mgr, const Comp& comp,
             detail::TreePtr<T> tree, std::size_t size)
      : mgr_(&mgr), comp_(&comp), tree_(std::move(tree)), size_(size) {}

  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const {
    auto hold = mgr_->acquire_hold();
    if (!tree_) return {*mgr_, tree_, *comp_};
    auto stack = cons(*mgr_, tree_, nullptr);
    while (stack->car->left) {
      stack = cons(*mgr_, stack->car->left, std::move(stack));
    }
    return {*mgr_, std::move(stack), *comp_};
  }

  iterator end() const { return cend(); }
  const_iterator cend() const { return {*mgr_, tree_, *comp_}; }

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
    auto s = detail::find(*mgr_, tree_, needle, *comp_);
    return s ? const_iterator(*mgr_, std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& needle) const {
    return static_cast<bool>(detail::find(*mgr_, tree_, needle, *comp_));
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
    auto result = detail::insert(*mgr_, tree_, std::move(t), *comp_, false);
    if (result.second) {
      return std::make_pair(
          mgr_->create<ManagedSet<T, Comp>>(token{}, *mgr_, *comp_,
                                            std::move(result.first), size_ + 1),
          true);
    } else {
      return std::make_pair(this->self(), false);
    }
  }

  template <typename... Args>
  std::pair<managed_ptr<ManagedSet<T, Comp>>, bool> emplace(Args&&... args) {
    auto hold = mgr_->acquire_hold();
    return insert(mgr_->create<T>(std::forward<Args>(args)...));
  }

  /**
   * Remove `val` from this set.
   *
   * Returns the resulting set and a flag that is true if the resulting set is
   * different than the current set (i.e. if `t` was already in this set).
   */
  template <typename U>
  std::pair<managed_ptr<ManagedSet<T, Comp>>, bool> erase(const U& val) const {
    auto hold = mgr_->acquire_hold();
    auto result = detail::erase(*mgr_, tree_, val, *comp_);
    if (result.second) {
      return std::make_pair(
          mgr_->create<ManagedSet<T, Comp>>(token{}, *mgr_, *comp_,
                                            std::move(result.first), size_ - 1),
          true);
    } else {
      return std::make_pair(this->self(), false);
    }
  }

 private:
  friend class MemoryManager;
  friend class testing::ManagedSetAccessor;

  MemoryManager* mgr_;
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

/**
 * Creates a `ManagedSet` with the given elements.
 *
 * All elements must be reachable or else this must be called with a hold.
 */
template <ManagedType T, typename Comp>
managed_ptr<ManagedSet<T, Comp>> managed_set(
    MemoryManager& mgr, const Comp& comp,
    std::initializer_list<managed_ptr<T>> els) {
  auto hold = mgr.acquire_hold();
  auto s = mgr.create<ManagedSet<T, Comp>>(mgr, comp);
  for (const auto& el : els) {
    s = s->insert(el).first;
  }
  return s;
}

/** @overload */
template <ManagedType T>
managed_ptr<ManagedSet<T>> managed_set(
    MemoryManager& mgr, std::initializer_list<managed_ptr<T>> els) {
  return managed_set(mgr, std::less<T>(), els);
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
template <ManagedType K, ManagedType V, typename Comp = std::less<K>>
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

  explicit ManagedMap(MemoryManager& mgr) : ManagedMap(mgr, Comp()) {}
  ManagedMap(MemoryManager& mgr, const Comp& comp)
      : ManagedMap(token{}, mgr, comp, nullptr, 0) {}
  /** Intended for private access only, but MemoryManager::create requires
   * access. Thus we pass a `token`. See https://abseil.io/tips/134. */
  ManagedMap(token, MemoryManager& mgr, const Comp& comp,
             detail::TreePtr<K, V> tree, std::size_t size)
      : mgr_(&mgr), comp_(&comp), tree_(std::move(tree)), size_(size) {}
  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const {
    auto hold = mgr_->acquire_hold();
    if (!tree_) return {*mgr_, tree_, *comp_};
    auto stack = cons(*mgr_, tree_, nullptr);
    while (stack->car->left) {
      stack = cons(*mgr_, stack->car->left, std::move(stack));
    }
    return {*mgr_, std::move(stack), *comp_};
  }

  iterator end() const { return cend(); }
  const_iterator cend() const { return {*mgr_, tree_, *comp_}; }

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
    auto s = detail::find(*mgr_, tree_, key, *comp_);
    return s ? const_iterator(*mgr_, std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& key) const {
    return static_cast<bool>(detail::find(*mgr_, tree_, key, *comp_));
  }

  template <typename U>
  std::optional<managed_ptr<V>> get(const U& key) const {
    auto s = detail::find(*mgr_, tree_, key, *comp_);
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
    auto hold = mgr_->acquire_hold();
    auto stack = detail::find(*mgr_, tree_, *k, *comp_);
    if (stack) {
      using T = detail::ManagedTree<K, V>;
      assert(!(*comp_)(*k, *stack->car->key()) &&
             !(*comp_)(*stack->car->key(), *k));
      auto old_value = std::make_optional(stack->car->value());
      detail::TreePtr<K, V> new_tree = T::make_tree(
          *mgr_, stack->car->left, stack->car->right,
          std::make_pair(std::move(k), std::move(v)), stack->car->color);
      while (stack->cdr) {
        stack = stack->cdr;
        const bool is_left = (*comp_)(*new_tree->key(), *stack->car->key());
        new_tree = T::make_tree(
            *mgr_, is_left ? std::move(new_tree) : stack->car->left,
            is_left ? stack->car->right : std::move(new_tree),
            stack->car->payload, stack->car->color);
      }
      return std::make_pair(
          mgr_->create<ManagedMap<K, V, Comp>>(token{}, *mgr_, *comp_,
                                               std::move(new_tree), size_),
          std::move(old_value));
    }
    auto result = detail::insert(
        *mgr_, tree_, std::make_pair(std::move(k), std::move(v)), *comp_, true);
    assert(result.second);
    return std::make_pair(
        mgr_->create<ManagedMap<K, V, Comp>>(
            token{}, *mgr_, *comp_, std::move(result.first), size_ + 1),
        std::nullopt);
  }

  template <typename KTuple, typename VTuple>
  std::pair<managed_ptr<ManagedMap<K, V, Comp>>, std::optional<managed_ptr<V>>>
  emplace(KTuple&& kargs, VTuple&& vargs) const {
    auto hold = mgr_->acquire_hold();
    return insert(
        std::apply(
            [&](auto&&... args) {
              return mgr_->create<K>(std::forward<decltype(args)>(args)...);
            },
            std::forward<KTuple>(kargs)),
        std::apply(
            [&](auto&&... args) {
              return mgr_->create<V>(std::forward<decltype(args)>(args)...);
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
    auto hold = mgr_->acquire_hold();
    auto result = detail::erase(*mgr_, tree_, key, *comp_);
    if (result.second) {
      return std::make_pair(
          mgr_->create<ManagedMap<K, V, Comp>>(
              token{}, *mgr_, *comp_, std::move(result.first), size_ - 1),
          std::move(result.second));
    } else {
      return std::make_pair(this->self(), std::nullopt);
    }
  }

 private:
  friend class testing::ManagedMapAccessor;

  MemoryManager* mgr_;
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

/**
 * Creates a `ManagedMap` with the given elements.
 *
 * All elements must be reachable or else this must be called with a hold.
 */
template <ManagedType K, ManagedType V, typename Comp>
managed_ptr<ManagedMap<K, V, Comp>> managed_map(
    MemoryManager& mgr, const Comp& comp,
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els) {
  auto hold = mgr.acquire_hold();
  auto m = mgr.create<ManagedMap<K, V, Comp>>(mgr, comp);
  for (const auto& el : els) {
    m = m->insert(el.first, el.second).first;
  }
  return m;
}

/** @overload */
template <ManagedType K, ManagedType V>
managed_ptr<ManagedMap<K, V>> managed_map(
    MemoryManager& mgr,
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els) {
  return managed_map(mgr, std::less<K>(), els);
}
}  // namespace emil::collections
