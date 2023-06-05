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
#include <vector>

#include "emil/cons.h"  // IWYU pragma: export
#include "emil/gc.h"
#include "emil/runtime.h"
#include "emil/tree.h"

/**
 * @file collections.h
 *
 * @brief Collections for memory-managed types.
 */

namespace emil::collections {

/** A fixed-size (mutable) array. */
// TODO: This might be horribly broken. The constructor is allocating
// space for the underlying type but new'ing managed_ptr into that
// memory. Also, managed_ptrs to elements can escape (e.g. through
// operator[]) without placing a reference on the array as a whole, so
// it can be deallocated out from under.
template <typename T>
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

  ~ManagedArray() { static_assert(ManagedType<T>); }

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

template <typename T>
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
concept is_constructible_from_tuple =
    requires(const Tuple& t) { is_constructible_from_tuple_impl<T>(t); };

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

template <ManagedType T>
ArrayPtr<T> to_array(const std::vector<managed_ptr<T>>& vec) {
  return make_managed<ManagedArray<T>>(
      vec.size(), [&vec](std::size_t i) { return vec[i]; });
}

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
 * See comments about `trees::tree_iterator`'s interaction with the
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
  using iterator = trees::tree_iterator<T, void, Comp>;
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
  ManagedSet(token, const Comp& comp, trees::TreePtr<T> tree, std::size_t size)
      : comp_(&comp), tree_(std::move(tree)), size_(size) {}

  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const { return iterator::begin(tree_, *comp_); }

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
    auto s = trees::find(tree_, needle, *comp_);
    return s ? const_iterator(std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& needle) const {
    return static_cast<bool>(trees::find(tree_, needle, *comp_));
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
    auto result = trees::insert(tree_, std::move(t), *comp_, false);
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
    auto result = trees::erase(tree_, val, *comp_);
    if (result.second) {
      return std::make_pair(
          make_managed<ManagedSet<T, Comp>>(token{}, *comp_,
                                            std::move(result.first), size_ - 1),
          true);
    } else {
      return std::make_pair(this->self(), false);
    }
  }

  /** Compute the union of l and r. */
  friend managed_ptr<ManagedSet> operator|(const managed_ptr<ManagedSet>& l,
                                           const managed_ptr<ManagedSet>& r) {
    if (l->empty()) return r;
    if (r->empty()) return l;
    auto hold = ctx().mgr->acquire_hold();
    trees::set_set_result_t<T, void> u;
    if (l->size() < r->size()) {
      u = union_right(r->tree_, black_height(r->tree_), l->tree_,
                      black_height(l->tree_), *l->comp_);
    } else {
      u = union_right(l->tree_, black_height(l->tree_), r->tree_,
                      black_height(r->tree_), *l->comp_);
    }
    return make_managed<ManagedSet>(token{}, *l->comp_, std::move(u.tree),
                                    l->size() + r->size() - u.count);
  }

  /** Compute the intersection of l and r. */
  friend managed_ptr<ManagedSet> operator&(const managed_ptr<ManagedSet>& l,
                                           const managed_ptr<ManagedSet>& r) {
    if (l->empty()) return l;
    if (r->empty()) return r;
    auto hold = ctx().mgr->acquire_hold();
    trees::set_set_result_t<T, void> u;
    if (l->size() < r->size()) {
      u = intersection_right(r->tree_, black_height(r->tree_), l->tree_,
                             black_height(l->tree_), *l->comp_);
    } else {
      u = intersection_right(l->tree_, black_height(l->tree_), r->tree_,
                             black_height(r->tree_), *l->comp_);
    }
    return make_managed<ManagedSet>(token{}, *l->comp_, std::move(u.tree),
                                    u.count);
  }

  /** Compute the set difference l - r. */
  friend managed_ptr<ManagedSet> operator-(managed_ptr<ManagedSet> l,
                                           managed_ptr<ManagedSet> r) {
    if (l->empty() || r->empty()) return l;
    auto hold = ctx().mgr->acquire_hold();
    if (l->size() < r->size()) {
      auto u = set_difference_right(r->tree_, black_height(r->tree_), l->tree_,
                                    black_height(l->tree_), *l->comp_);
      return make_managed<ManagedSet>(token{}, *l->comp_, std::move(u.tree),
                                      u.count);
    } else {
      auto u = set_difference_left(l->tree_, black_height(l->tree_), r->tree_,
                                   black_height(r->tree_), *l->comp_);
      return make_managed<ManagedSet>(token{}, *l->comp_, std::move(u.tree),
                                      l->size() - u.count);
    }
  }

 private:
  friend class MemoryManager;
  friend class testing::ManagedSetAccessor;
  template <ManagedType K, ManagedType V, typename C>
  friend class ManagedMap;

  const Comp* comp_;
  trees::TreePtr<T> tree_;
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
template <ManagedType T, typename Comp>
SetPtr<T, Comp> managed_set(const Comp& comp) {
  return managed_set<T>(comp, {});
}

/** @overload */
template <ManagedType T>
SetPtr<T> managed_set(std::initializer_list<managed_ptr<T>> els) {
  return managed_set(std::less<>(), els);
}

/** @overload */
template <ManagedType T>
SetPtr<T> managed_set() {
  return managed_set<T>(std::less<>());
}

/**
 * A map whose keys and values are managed, with O(lg n) insertion and deletion
 * times.
 *
 * This map is immutable and *persistent* in the sense described in
 * https://en.wikipedia.org/wiki/Persistent_data_structure.
 *
 * See comments about `trees::tree_iterator`'s interaction with the memory
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
  using iterator = trees::tree_iterator<K, V, Comp>;
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
  ManagedMap(token, const Comp& comp, trees::TreePtr<K, V> tree,
             std::size_t size)
      : comp_(&comp), tree_(std::move(tree)), size_(size) {}
  iterator begin() const { return cbegin(); }
  const_iterator cbegin() const { return iterator::begin(tree_, *comp_); }

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
    auto s = trees::find(tree_, key, *comp_);
    return s ? const_iterator(std::move(s), *comp_) : cend();
  }

  template <typename U>
  bool contains(const U& key) const {
    return static_cast<bool>(trees::find(tree_, key, *comp_));
  }

  template <typename U>
  std::optional<managed_ptr<V>> get(const U& key) const {
    auto s = trees::find(tree_, key, *comp_);
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
    auto stack = trees::find(tree_, *k, *comp_);
    if (stack) {
      using T = trees::ManagedTree<K, V>;
      assert(!(*comp_)(*k, *stack->car->key()) &&
             !(*comp_)(*stack->car->key(), *k));
      auto old_value = std::make_optional(stack->car->value());
      trees::TreePtr<K, V> new_tree = T::make_tree(
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
    auto result = trees::insert(
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
    auto result = trees::erase(tree_, key, *comp_);
    if (result.second) {
      return std::make_pair(
          make_managed<ManagedMap<K, V, Comp>>(
              token{}, *comp_, std::move(result.first), size_ - 1),
          std::move(result.second));
    } else {
      return std::make_pair(this->self(), std::nullopt);
    }
  }

  /**
   * @brief Compute the union of l and r.
   *
   * For any `key` that is in `l` and `r`, the mapping from `r` will be used.
   */
  friend managed_ptr<ManagedMap> operator|(managed_ptr<ManagedMap> l,
                                           managed_ptr<ManagedMap> r) {
    if (l->empty()) return r;
    if (r->empty()) return l;
    auto hold = ctx().mgr->acquire_hold();
    trees::set_set_result_t<K, V> u;
    if (l->size() < r->size()) {
      u = union_left(r->tree_, black_height(r->tree_), l->tree_,
                     black_height(l->tree_), *l->comp_);
    } else {
      u = union_right(l->tree_, black_height(l->tree_), r->tree_,
                      black_height(r->tree_), *l->comp_);
    }
    return make_managed<ManagedMap>(token{}, *l->comp_, std::move(u.tree),
                                    l->size() + r->size() - u.count);
  }

  /** Compute the intersection of l and r using the values from r. */
  friend managed_ptr<ManagedMap> operator&(managed_ptr<ManagedMap> l,
                                           managed_ptr<ManagedMap> r) {
    if (l->empty()) return l;
    if (r->empty()) return r;
    auto hold = ctx().mgr->acquire_hold();
    trees::set_set_result_t<K, V> u;
    if (l->size() < r->size()) {
      u = intersection_left(r->tree_, black_height(r->tree_), l->tree_,
                            black_height(l->tree_), *l->comp_);
    } else {
      u = intersection_right(l->tree_, black_height(l->tree_), r->tree_,
                             black_height(r->tree_), *l->comp_);
    }
    return make_managed<ManagedMap>(token{}, *l->comp_, std::move(u.tree),
                                    u.count);
  }

  /**
   * Filter the keys in this map by a set of keys.
   *
   * The returned map has all the keys that are in both `keys` and
   * `this`, mapped to the same values as in `this`.
   */
  managed_ptr<ManagedMap> filter_keys(SetPtr<K, Comp> keys) {
    if (empty()) return this->self();
    if (keys->empty()) return make_managed<ManagedMap>(*comp_);
    auto hold = ctx().mgr->acquire_hold();
    trees::set_set_result_t<K, V> u;
    if (keys->size() < size()) {
      u = intersection_left(tree_, black_height(tree_), keys->tree_,
                            black_height(keys->tree_), *comp_);
    } else {
      u = intersection_right(keys->tree_, black_height(keys->tree_), tree_,
                             black_height(tree_), *comp_);
    }
    return make_managed<ManagedMap>(token{}, *comp_, std::move(u.tree),
                                    u.count);
  }

  /** Compute the set difference l - r. */
  friend managed_ptr<ManagedMap> operator-(managed_ptr<ManagedMap> l,
                                           managed_ptr<ManagedMap> r) {
    if (l->empty() || r->empty()) return l;
    auto hold = ctx().mgr->acquire_hold();
    if (l->size() < r->size()) {
      auto u = set_difference_right(r->tree_, black_height(r->tree_), l->tree_,
                                    black_height(l->tree_), *l->comp_);
      return make_managed<ManagedMap>(token{}, *l->comp_, std::move(u.tree),
                                      u.count);
    } else {
      auto u = set_difference_left(l->tree_, black_height(l->tree_), r->tree_,
                                   black_height(r->tree_), *l->comp_);
      return make_managed<ManagedMap>(token{}, *l->comp_, std::move(u.tree),
                                      l->size() - u.count);
    }
  }

 private:
  friend class testing::ManagedMapAccessor;

  const Comp* comp_;
  trees::TreePtr<K, V> tree_;
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
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els = {}) {
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
    std::initializer_list<std::pair<managed_ptr<K>, managed_ptr<V>>> els = {}) {
  return managed_map(std::less<>(), els);
}
}  // namespace emil::collections
