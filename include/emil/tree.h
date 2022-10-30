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

#include "emil/cons.h"
#include "emil/gc.h"
#include "emil/runtime.h"

namespace emil::collections::trees {

// TODO: There's some inconsistencies in ordering between left
// subtree, right subtree, and payload in the various functions that
// build tree (e.g. balance, make_tree, rotate, join). These should be
// fixed.

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
 * @brief Trees with a key, used for sorting, and a side value, ignored for
 * sorting.
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

  static maybe_value_type maybe_value(value_type v) {
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
 * @brief Specialization for "sets" -- trees with just keys, no side values.
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

template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> to_black(const TreePtr<K, V>& t) {
  return ManagedTree<K, V>::make_tree(t->left, t->right, t->payload,
                                      Color::Black);
}

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
 * @brief Iterates over a `ManagedTree`.
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
    return T::make_tree(to_black(left->left),
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
                        to_black(right->right), right->payload, Color::Red);
  }
  return T::make_tree(std::move(left), std::move(right), std::move(payload),
                      color);
}

/**
 * @brief Possibly replace `tree` with a new tree with equivalent payload.
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
    return to_black(std::move(tree));
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
  return to_black(std::move(tree));
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
      return std::make_pair(to_black(tree->right), tree->payload);
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
      return std::make_pair(to_black(tree->left), tree->value());
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
    // to_red
    return T::make_tree(tree->left, tree->right, tree->payload, Color::Red);
  } else {
    return tree;
  }
}

/**
 * @brief Delete `key` from `tree`.
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

template <ManagedType K, OptionalManagedType V>
std::size_t black_height(TreePtr<K, V> tree) {
  std::size_t height = 0;
  while (tree) {
    height += tree->color == Color::Black;
    tree = tree->left;
  }
  return height;
}

/**
 * @brief Join left and right on mid.
 *
 * Preconditions:
 * 0. There is a hold on the memory manager.
 * 1. All keys in left are less than key(mid).
 * 2. key(mid) is less than all keys in right.
 * 3. left_height == black_height(left)
 * 4. right_height == black_height(right)
 * 5. left_height >= right_height
 *
 * Postconditions:
 * 0. The result contains all elements from left and right along with mid.
 * 1. The black height of the result is left_height.
 * 2. The local RB invariant may be broken at the root of the result by the root
 * being red with the right child being red.
 * 3. The size of the tree is one more than the sum of the sizes of left and
 * right.
 */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> join_right(TreePtr<K, V> left, std::size_t left_height,
                         typename ManagedTree<K, V>::payload_type&& mid,
                         TreePtr<K, V> right, std::size_t right_height) {
  assert(left_height == black_height(left));
  assert(right_height == black_height(right));
  assert(left_height >= right_height);
  using T = ManagedTree<K, V>;
  if (!left || (left->color == Color::Black && left_height == right_height)) {
    return T::make_tree(std::move(left), std::move(right), std::move(mid),
                        Color::Red);
  }
  assert(left->color != Color::DoubleBlack);
  auto t = join_right(left->right, left_height - (left->color == Color::Black),
                      std::move(mid), std::move(right), right_height);
  if (left->color == Color::Black && t && t->right && t->color == Color::Red &&
      t->right->color == Color::Red) {
    auto new_left =
        T::make_tree(left->left, t->left, left->payload, Color::Black);
    return T::make_tree(std::move(new_left), to_black(t->right), t->payload,
                        Color::Red);
  }
  return T::make_tree(left->left, std::move(t), left->payload, left->color);
}

/**
 * @brief Join left and right on mid.
 *
 * Preconditions:
 * 0. There is a hold on the memory manager.
 * 1. All keys in left are less than key(mid).
 * 2. key(mid) is less than all keys in right.
 * 3. left_height == black_height(left)
 * 4. right_height == black_height(right)
 * 5. left_height <= right_height
 *
 * Postconditions:
 * 0. The result contains all elements from left and right along with mid.
 * 1. The black height of the result is right_height.
 * 2. The local RB invariant may be broken at the root of the result by the root
 * being red with the left child being red.
 */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> join_left(TreePtr<K, V> left, std::size_t left_height,
                        typename ManagedTree<K, V>::payload_type&& mid,
                        TreePtr<K, V> right, std::size_t right_height) {
  assert(left_height == black_height(left));
  assert(right_height == black_height(right));
  assert(left_height <= right_height);
  using T = ManagedTree<K, V>;
  if (!right || (right->color == Color::Black && left_height == right_height)) {
    return T::make_tree(std::move(left), std::move(right), std::move(mid),
                        Color::Red);
  }
  assert(right->color != Color::DoubleBlack);
  auto t = join_left(std::move(left), left_height, std::move(mid), right->left,
                     right_height - (right->color == Color::Black));
  if (right->color == Color::Black && t && t->left && t->color == Color::Red &&
      t->left->color == Color::Red) {
    auto new_right =
        T::make_tree(t->right, right->right, right->payload, Color::Black);
    return T::make_tree(to_black(t->left), std::move(new_right), t->payload,
                        Color::Red);
  }
  return T::make_tree(std::move(t), right->right, right->payload, right->color);
}

/**
 * @brief Join left and right on mid.
 *
 * Preconditions:
 * 0. There is a hold on the memory manager.
 * 1. All keys in left are less than key(mid).
 * 2. key(mid) is less than all keys in right.
 * 3. left_height == black_height(left)
 * 4. right_height == black_height(right)
 * 5. left_height <= right_height
 *
 * Postconditions:
 * 0. The resulting tree contains all elements from left and right along with
 * mid.
 * 1. The black height of the resulting tree is the second element of the pair.
 */
template <ManagedType K, OptionalManagedType V>
std::pair<TreePtr<K, V>, std::size_t> join(
    TreePtr<K, V> left, std::size_t left_height,
    typename ManagedTree<K, V>::payload_type mid, TreePtr<K, V> right,
    std::size_t right_height) {
  using T = ManagedTree<K, V>;
  if (left_height < right_height) {
    auto tree = join_left(std::move(left), left_height, std::move(mid),
                          std::move(right), right_height);
    if (tree->color == Color::Red && tree->left &&
        tree->left->color == Color::Red) {
      return std::make_pair(to_black(std::move(tree)), right_height + 1);
    }
    return std::make_pair(std::move(tree), right_height);
  } else if (right_height < left_height) {
    auto tree = join_right(std::move(left), left_height, std::move(mid),
                           std::move(right), right_height);
    if (tree->color == Color::Red && tree->right &&
        tree->right->color == Color::Red) {
      return std::make_pair(to_black(std::move(tree)), left_height + 1);
    }
    return std::make_pair(std::move(tree), left_height);
  }
  if ((!left || left->color == Color::Black) &&
      (!right || right->color == Color::Black)) {
    return std::make_pair(T::make_tree(std::move(left), std::move(right),
                                       std::move(mid), Color::Red),
                          left_height);
  }
  return std::make_pair(T::make_tree(std::move(left), std::move(right),
                                     std::move(mid), Color::Black),
                        left_height + 1);
}

template <ManagedType K, OptionalManagedType V>
struct split_result_t {
  TreePtr<K, V> left;
  std::size_t left_height;
  TreePtr<K, V> right;
  std::size_t right_height;
  typename ManagedTree<K, V>::maybe_value_type found;
};

/**
 * @brief Split `tree` by `key`.
 *
 * The result is a left tree, with keys less than `key`, and a right tree,
 * with keys greater than `key`. Returns the existing mapping, if any.
 *
 * Must be called with a hold on the memory manager.
 */
template <ManagedType K, OptionalManagedType V, typename Comp>
split_result_t<K, V> split(TreePtr<K, V> tree, std::size_t height, const K& key,
                           const Comp& comp) {
  using T = ManagedTree<K, V>;
  if (!tree) {
    assert(height == 0);
    return {nullptr, 0, nullptr, 0, T::no_value()};
  }
  const std::size_t subtree_height = height - (tree->color == Color::Black);
  if (comp(key, *tree->key())) {
    auto result = split(tree->left, subtree_height, key, comp);
    std::tie(result.right, result.right_height) =
        join(result.right, result.right_height, tree->payload, tree->right,
             subtree_height);
    return result;
  } else if (comp(*tree->key(), key)) {
    auto result = split(tree->right, subtree_height, key, comp);
    std::tie(result.left, result.left_height) =
        join(tree->left, subtree_height, tree->payload, result.left,
             result.left_height);
    return result;
  }
  return {tree->left, subtree_height, tree->right, subtree_height,
          T::maybe_value(tree->value())};
}

template <ManagedType K, OptionalManagedType V>
struct union_result_t {
  TreePtr<K, V> tree;
  /** black height of tree. */
  std::size_t height;
  /** The number of keys that were in both left and right. */
  std::size_t num_overlaps;
};

/**
 * @brief Computes the union of two sets or maps, preferring values from the
 * right.
 *
 * right should be smaller than left for peak efficiency.
 *
 * Must be called with a hold on the memory manager.
 */
template <ManagedType K, OptionalManagedType V, typename Comp>
union_result_t<K, V> union_right(TreePtr<K, V> left, std::size_t left_height,
                                 TreePtr<K, V> right, std::size_t right_height,
                                 const Comp& comp) {
  if (!left) return {std::move(right), right_height, 0};
  if (!right) return {std::move(left), left_height, 0};
  auto s = split(std::move(left), left_height, *right->key(), comp);
  const std::size_t right_subtree_height =
      right_height - (right->color == Color::Black);
  auto l = union_right(std::move(s.left), s.left_height, right->left,
                       right_subtree_height, comp);
  auto r = union_right(std::move(s.right), s.right_height, right->right,
                       right_subtree_height, comp);
  auto j = join(std::move(l.tree), l.height, right->payload, std::move(r.tree),
                r.height);
  return {std::move(j.first), j.second,
          l.num_overlaps + r.num_overlaps + static_cast<bool>(s.found)};
}

/**
 * @brief Computes the union of two maps, preferring values from the left.
 *
 * left should be smaller than right for peak efficiency.
 *
 * Must be called with a hold on the memory manager.
 */
template <ManagedType K, ManagedType V, typename Comp>
union_result_t<K, V> union_left(TreePtr<K, V> left, std::size_t left_height,
                                TreePtr<K, V> right, std::size_t right_height,
                                const Comp& comp) {
  if (!left) return {std::move(right), right_height, 0};
  if (!right) return {std::move(left), left_height, 0};
  auto s = split(std::move(right), right_height, *left->key(), comp);
  const std::size_t left_subtree_height =
      left_height - (left->color == Color::Black);
  auto l = union_left(left->left, left_subtree_height, std::move(s.left),
                      s.left_height, comp);
  auto r = union_left(left->right, left_subtree_height, std::move(s.right),
                      s.right_height, comp);
  auto j = join(std::move(l.tree), l.height, left->payload, std::move(r.tree),
                r.height);
  return {std::move(j.first), j.second,
          l.num_overlaps + r.num_overlaps + static_cast<bool>(s.found)};
}

}  // namespace emil::collections::trees
