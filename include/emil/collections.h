
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
    visitor(car);
    visitor(cdr);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedCons);
  }
};

template <ManagedType T>
using ConsPtr = managed_ptr<ManagedCons<T>>;

template <ManagedType T>
ConsPtr<T> cons(MemoryManager& mgr, managed_ptr<T> car, ConsPtr<T> cdr) {
  return mgr.create<ManagedCons<T>>(std::move(car), std::move(cdr));
}

template <ManagedType T>
ConsPtr<T> cons(MemoryManager& mgr, managed_ptr<T> car, std::nullptr_t) {
  return mgr.create<ManagedCons<T>>(std::move(car), nullptr);
}

template <ManagedType T>
ConsPtr<T> cons(MemoryManager& mgr, std::nullptr_t, ConsPtr<T> cdr) {
  return mgr.create<ManagedCons<T>>(nullptr, std::move(cdr));
}

namespace detail {

enum class Color { Red, Black };

/** A red-black tree for managed types. */
template <ManagedType K, OptionalManagedType V = void>
struct ManagedTree;  // IWYU pragma: keep

template <ManagedType K, OptionalManagedType V = void>
using TreePtr = managed_ptr<ManagedTree<K, V>>;

/** Trees with a key, used for sorting, and a side value. */
template <ManagedType K, OptionalManagedType V>
struct ManagedTree : Managed {
  TreePtr<K, V> left;
  TreePtr<K, V> right;
  managed_ptr<K> key;
  managed_ptr<V> val;
  Color color;

  ManagedTree(TreePtr<K, V>&& left, TreePtr<K, V>&& right, managed_ptr<K>&& key,
              managed_ptr<V>&& val, Color color)
      : left(std::move(left)),
        right(std::move(right)),
        key(std::move(key)),
        val(std::move(val)),
        color(color) {}

  void visit_subobjects(const ManagedVisitor& visitor) override {
    visitor(left);
    visitor(right);
    visitor(key);
    visitor(val);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedTree);
  }
};

/** Specialization for "sets" -- trees with just keys, no side values. */
template <ManagedType K>
struct ManagedTree<K, void> : Managed {
  TreePtr<K, void> left;
  TreePtr<K, void> right;
  managed_ptr<K> key;
  Color color;

  ManagedTree(TreePtr<K, void>&& left, TreePtr<K, void>&& right,
              managed_ptr<K>&& key, Color color)
      : left(std::move(left)),
        right(std::move(right)),
        key(std::move(key)),
        color(color) {}

  void visit_subobjects(const ManagedVisitor& visitor) override {
    visitor(left);
    visitor(right);
    visitor(key);
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedTree);
  }
};

/** Invariants: Red trees have no red children, black depth of both subtrees is
 * the same. */
template <ManagedType K, OptionalManagedType V>
int verify_subtree_invariants(const TreePtr<K, V>& subtree) {
  if (!subtree) return 1;
  if (subtree->color == Color::Red &&
      ((subtree->left && subtree->left->color == Color::Red) ||
       (subtree->right && subtree->right->color == Color::Red))) {
    throw std::logic_error("Red node has red child.");
  }
  int ldepth = verify_subtree_invariants(subtree->left);
  if (ldepth != verify_subtree_invariants(subtree->right)) {
    throw std::logic_error(
        "Left and right subtrees have different black depth.");
  }
  return ldepth + (subtree->color == Color::Black);
}

/** Invariants: Subtree invariants plus the root is black. */
template <ManagedType K, OptionalManagedType V>
bool verify_invariants(const TreePtr<K, V>& root) {
  if (!root) return true;
  if (root->color == Color::Red) {
    throw std::logic_error("Root is red.");
  }
  verify_subtree_invariants(root);
  return true;
}

/**
 * A helper class to allow the same code to be used for both key and
 * key-value trees.
 *
 * The payload for a node in the tree is the key and, if present, the
 * value.
 */
template <ManagedType K, OptionalManagedType V>
struct Payload {
  typedef std::pair<managed_ptr<K>, managed_ptr<V>> type;

  static type get(const ManagedTree<K, V>& tree) {
    return std::make_pair(tree.key, tree.value);
  }

  static const managed_ptr<K>& key(const type& payload) {
    return payload.first;
  }

  static TreePtr<K, V> make_tree(MemoryManager& mgr, TreePtr<K, V> left,
                                 TreePtr<K, V> right, type&& payload,
                                 Color color) {
    return mgr.create<ManagedTree<K, V>>(std::move(left), std::move(right),
                                         std::move(payload.first),
                                         std::move(payload.second), color);
  }
};

template <ManagedType K>
struct Payload<K, void> {
  typedef managed_ptr<K> type;

  static const type& get(const ManagedTree<K, void>& tree) { return tree.key; }

  static const managed_ptr<K>& key(const type& payload) { return payload; }

  static TreePtr<K, void> make_tree(MemoryManager& mgr, TreePtr<K, void> left,
                                    TreePtr<K, void> right, type key,
                                    Color color) {
    return mgr.create<ManagedTree<K, void>>(std::move(left), std::move(right),
                                            std::move(key), color);
  }
};

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
  using value_type = typename Payload<K, V>::type;
  using reference = const value_type&;

 public:
  tree_iterator() : mgr_(nullptr), stack_(nullptr), comp_(nullptr) {}
  tree_iterator(MemoryManager& mgr, TreeStack<K, V> stack, const Comp& comp)
      : mgr_(&mgr), stack_(std::move(stack)), comp_(&comp) {}
  /** Creates an end iterator for `tree`. */
  tree_iterator(MemoryManager& mgr, TreePtr<K, V> tree, const Comp& comp)
      : tree_iterator(mgr,
                      cons(mgr, nullptr, cons(mgr, std::move(tree), nullptr)),
                      comp) {}

  reference operator*() const { return Payload<K, V>::get(*stack_->car); }

  tree_iterator& operator++() {
    if (stack_->car->right) {
      auto hold = mgr_->acquire_hold();
      stack_ = cons(*mgr_, stack_->car->right, stack_);
      while (stack_->car->left) {
        stack_ = cons(*mgr_, stack_->car->left, stack_);
      }
    } else {
      while (stack_->cdr && (*comp_)(*stack_->cdr->car->key, *stack_->car->key))
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
    while (stack_->cdr && (*comp_)(*stack_->car->key, *stack_->cdr->car->key))
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

template <typename T, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find(TreePtr<K, V> tree, const T& key,
                     const TreeStack<K, V>& lower_bound, const Comp& comp,
                     TreeStack<K, V> stack) {
  if (!tree) return comp(*lower_bound->car->key, key) ? nullptr : lower_bound;
  if (comp(key, *tree->key))
    return find(tree->left, key, lower_bound, comp,
                cons(tree, std::move(stack)));
  return find(tree->right, key, tree, comp, cons(tree, std::move(stack)));
}

/** Find the key in the tree, returning the path from root to the node
 * containing the key. Returns nullptr if not found. */
template <typename T, ManagedType K, OptionalManagedType V, typename Comp>
TreeStack<K, V> find(TreePtr<K, V> tree, const T& key, const Comp& comp,
                     TreeStack<K, V> stack = nullptr) {
  if (!tree) return nullptr;
  if (comp(key, *tree->key))
    return find(tree->left, key, comp, cons(tree, std::move(stack)));
  return find(tree->right, key, tree, comp, cons(tree, std::move(stack)));
}

/** Balance a red-black tree when inserting in the left-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_ll(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename Payload<K, V>::type payload) {
  using P = Payload<K, V>;
  if (color == Color::Black && left && left->left &&
      left->color == Color::Red && left->left->color == Color::Red) {
    return P::make_tree(mgr,
                        P::make_tree(mgr, left->left->left, left->left->right,
                                     P::get(*left->left), Color::Black),
                        P::make_tree(mgr, left->right, std::move(right),
                                     std::move(payload), Color::Black),
                        P::get(*left), Color::Red);
  }
  return P::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the left-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_lr(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename Payload<K, V>::type payload) {
  using P = Payload<K, V>;
  if (color == Color::Black && left && left->right &&
      left->color == Color::Red && left->right->color == Color::Red) {
    return P::make_tree(mgr,
                        P::make_tree(mgr, left->left, left->right->left,
                                     P::get(*left), Color::Black),
                        P::make_tree(mgr, left->right->right, std::move(right),
                                     std::move(payload), Color::Black),
                        P::get(*left->right), Color::Red);
  }
  return P::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the right-left grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rl(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename Payload<K, V>::type payload) {
  using P = Payload<K, V>;
  if (color == Color::Black && right && right->left &&
      right->color == Color::Red && right->left->color == Color::Red) {
    return P::make_tree(mgr,
                        P::make_tree(mgr, std::move(left), right->left->left,
                                     std::move(payload), Color::Black),
                        P::make_tree(mgr, right->left->right, right->right,
                                     P::get(*right), Color::Black),
                        P::get(*right->left), Color::Red);
  }
  return P::make_tree(mgr, std::move(left), std::move(right),
                      std::move(payload), color);
}

/** Balance a red-black tree when inserting in the right-right grandchild. */
template <ManagedType K, OptionalManagedType V>
TreePtr<K, V> balance_rr(MemoryManager& mgr, Color color, TreePtr<K, V> left,
                         TreePtr<K, V> right,
                         typename Payload<K, V>::type payload) {
  using P = Payload<K, V>;
  if (color == Color::Black && right && right->right &&
      right->color == Color::Red && right->right->color == Color::Red) {
    return P::make_tree(
        mgr,
        P::make_tree(mgr, std::move(left), right->left, std::move(payload),
                     Color::Black),
        P::make_tree(mgr, right->right->left, right->right->right,
                     P::get(*right->right), Color::Black),
        P::get(*right), Color::Red);
  }
  return P::make_tree(mgr, std::move(left), std::move(right),
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
    typename Payload<K, V>::type&& payload, bool replace) {
  if (replace) {
    return Payload<K, V>::make_tree(mgr, tree->left, tree->right,
                                    std::move(payload), tree->color);
  }
  return std::nullopt;
}

template <ManagedType K, OptionalManagedType V, typename Comp>
std::optional<TreePtr<K, V>> insert_into_subtree(
    MemoryManager& mgr, TreePtr<K, V> tree,
    typename Payload<K, V>::type&& payload, const Comp& comp, bool replace) {
  using P = Payload<K, V>;
  if (!tree) {
    return P::make_tree(mgr, nullptr, nullptr, std::move(payload), Color::Red);
  }
  const auto& key = P::key(payload);
  if (comp(*key, *tree->key)) {
    const bool not_less_than_left = tree->left && !comp(*key, *tree->left->key);
    if (not_less_than_left && !comp(*tree->left->key, *key)) {
      return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(mgr, tree->left, std::move(payload), comp,
                               replace)
        .transform([&](auto&& new_tree) {
          if (!tree->left) {
            return P::make_tree(mgr, std::move(new_tree), tree->right,
                                P::get(*tree), tree->color);
          } else if (not_less_than_left) {
            return balance_lr(mgr, tree->color, std::move(new_tree),
                              tree->right, P::get(*tree));
          } else {
            return balance_ll(mgr, tree->color, std::move(new_tree),
                              tree->right, P::get(*tree));
          }
        });
  } else if (comp(*tree->key, *key)) {
    const bool not_less_than_right =
        tree->right && !comp(*key, *tree->right->key);
    if (not_less_than_right && !comp(*tree->right->key, *key)) {
      return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
    }
    return insert_into_subtree(mgr, tree->right, std::move(payload), comp,
                               replace)
        .transform([&](auto&& new_tree) {
          if (!tree->right) {
            return P::make_tree(mgr, tree->left, std::move(new_tree),
                                P::get(*tree), tree->color);
          } else if (not_less_than_right) {
            return balance_rr(mgr, tree->color, tree->left, std::move(new_tree),
                              P::get(*tree));
          } else {
            return balance_rl(mgr, tree->color, tree->left, std::move(new_tree),
                              P::get(*tree));
          }
        });
  } else {
    return maybe_replace(mgr, std::move(tree), std::move(payload), replace);
  }
}

/** Insert `payload` into `tree`. */
template <ManagedType K, OptionalManagedType V, typename Comp>
std::pair<TreePtr<K, V>, bool> insert(MemoryManager& mgr, TreePtr<K, V> tree,
                                      typename Payload<K, V>::type&& payload,
                                      const Comp& comp, bool replace) {
  assert(verify_invariants(tree));
  auto hold = mgr.acquire_hold();
  auto result =
      *insert_into_subtree(mgr, tree, std::move(payload), comp, replace)
           .transform([&](auto&& new_tree) {
             if (new_tree->color == Color::Black) {
               return std::make_pair(std::move(new_tree), true);
             } else {
               using P = Payload<K, V>;
               return std::make_pair(
                   P::make_tree(mgr, new_tree->left, new_tree->right,
                                P::get(*new_tree), Color::Black),
                   true);
             }
           })
           .or_else([&]() {
             return std::make_optional(std::make_pair(std::move(tree), false));
           });
  assert(verify_invariants(tree));
  return result;
}

}  // namespace detail

namespace testing {
class ManagedSetAccessor;
}

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

  /**
   * Insert `t` into this set.
   *
   * Returns the resulting set and a flag that is true if the
   * resulting set is different than the current set (i.e. if `t` was
   * not already in this set.)
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

 private:
  friend class MemoryManager;
  friend class testing::ManagedSetAccessor;

  MemoryManager* mgr_;
  const Comp* comp_;
  detail::TreePtr<T> tree_;
  std::size_t size_ = 0;

  void visit_subobjects(const ManagedVisitor& visitor) override {
    visitor(tree_);
    if constexpr (ManagedType<Comp>) {
      visitor(*comp_);
    }
  }

  std::size_t managed_size() const noexcept override {
    return sizeof(ManagedSet);
  }
};

template <ManagedType T, typename Comp>
managed_ptr<ManagedSet<T, Comp>> managed_set(
    MemoryManager& mgr, const Comp& comp,
    std::initializer_list<managed_ptr<T>> els) {
  auto s = mgr.create<ManagedSet<T, Comp>>(mgr, comp);
  for (const auto& el : els) {
    s = s->insert(el).first;
  }
  return s;
}

template <ManagedType T>
managed_ptr<ManagedSet<T>> managed_set(
    MemoryManager& mgr, std::initializer_list<managed_ptr<T>> els) {
  return managed_set(mgr, std::less<T>(), els);
}

}  // namespace emil::collections
