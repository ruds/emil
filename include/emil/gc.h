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
#include <cstdint>
#include <iosfwd>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>

#include "emil/runtime.h"

namespace emil {

class managed_ptr_base;

/** Returns true if subobjects should be visited. */
class ManagedVisitor {
 public:
  ManagedVisitor();
  virtual ~ManagedVisitor();

 private:
  friend class managed_ptr_base;

  virtual bool visit(const managed_ptr_base& ptr) const = 0;

  ManagedVisitor(const ManagedVisitor&) = delete;
  ManagedVisitor& operator=(const ManagedVisitor&) = delete;
  ManagedVisitor(ManagedVisitor&&) = delete;
  ManagedVisitor& operator=(ManagedVisitor&&) = delete;
};

/**
 * Base class for all objects managed by emil's memory manager.
 *
 * Managed objects should only be created by MemoryManger::create.
 * Managed objects should not allocate any memory directly or
 * indirectly except through the MemoryManager interface. In
 * particular, shareable subobjects (e.g. one of the entries in a
 * tuple or record) should be refered to through `managed_ptr`, and
 * non-sharable subobjects (e.g. the buffer underlying a string)
 * should either be allocated using automatic storage duration (i.e.
 * as a field without dynamic allocation) or through a function like
 * MemoryManager::allocate_private_buffer.
 */
class Managed {
 public:
  virtual ~Managed();

 protected:
  Managed();

 private:
  friend class MemoryManager;
  friend class managed_ptr_base;

  mutable std::uintptr_t next_managed_ =
      reinterpret_cast<std::uintptr_t>(nullptr);

  Managed(const Managed&) = delete;
  Managed& operator=(const Managed&) = delete;

  /**
   * Visits all the managed subobjects of this object.
   *
   * Implementations should pass the visitor to the accept method of
   * each managed_ptr they own.
   *
   * This could be used, for example, in the mark phase of a mark &
   * sweep garbage collector to mark all the objects accessible
   * through this object.
   */
  virtual void visit_subobjects(const ManagedVisitor& visitor) = 0;

  /**
   * The allocated size of the object.
   *
   * Concrete subclasses should implement this as `return sizeof(ClassName);`
   */
  virtual std::size_t managed_size() const noexcept = 0;

  bool mark() const;
  /** Updates the next_managed pointer and clears the mark. */
  void update_next_managed_and_clear(Managed* next) const;
  bool is_marked() const;
  Managed* next_managed() const;
};

template <typename T>
class ManagedWithSelfPtr;

namespace detail {

template <typename T>
void is_managed_with_self_ptr_impl(const ManagedWithSelfPtr<T>&);

template <typename T>
concept is_managed_with_self_ptr =
    requires(const T& t) { is_managed_with_self_ptr_impl<T>(t); };
}  // namespace detail

template <typename T>
concept ManagedType =
    std::is_base_of<Managed, T>::value || detail::is_managed_with_self_ptr<T>;

template <typename U, typename T>
concept BaseManagedType =
    ManagedType<T> && ManagedType<U> && std::is_base_of<T, U>::value;

template <typename T>
concept OptionalManagedType = ManagedType<T> || std::is_same_v<T, void>;

/**
 * A type-erased pointer to Managed. Use managed_ptr<T> for almost all
 * purposes.
 */
class managed_ptr_base {
 public:
  ~managed_ptr_base();
  Managed& operator*() { return *val_; }
  const Managed& operator*() const { return *val_; }
  Managed* operator->() { return val_; }
  const Managed* operator->() const { return val_; }

  void accept(const ManagedVisitor& visitor) const;

  explicit operator bool() const noexcept { return val_; }

  friend bool operator==(const managed_ptr_base& l, const managed_ptr_base& r) {
    return l.val_ == r.val_;
  }

 protected:
  Managed* val_;

  explicit managed_ptr_base(Managed* val) noexcept;

 private:
  friend class MemoryManager;
  friend class MarkVisitor;

  bool mark() const;
};

static_assert(sizeof(managed_ptr_base) == sizeof(void*));

/**
 * A pointer to a managed object.
 *
 * Users of this interface must not capture the address of the managed
 * object in a way that may outlive the lifetime of the managed_ptr.
 */
template <typename T>
class managed_ptr : public managed_ptr_base {
 public:
  managed_ptr() noexcept : managed_ptr(nullptr) {}
  // cppcheck-suppress noExplicitConstructor
  managed_ptr(std::nullptr_t) noexcept : managed_ptr_base(nullptr) {}

  template <BaseManagedType<T> U>
  // cppcheck-suppress noExplicitConstructor
  managed_ptr(managed_ptr<U>&& o) noexcept : managed_ptr_base(o.val_) {}

  template <BaseManagedType<T> U>
  managed_ptr& operator=(managed_ptr<U>&& o) noexcept {
    val_ = o.val_;
    return *this;
  }

  template <BaseManagedType<T> U>
  // cppcheck-suppress noExplicitConstructor
  managed_ptr(const managed_ptr<U>& o) noexcept : managed_ptr_base(o.val_) {}

  template <BaseManagedType<T> U>
  managed_ptr& operator=(const managed_ptr<U>& o) noexcept {
    val_ = o.val_;
    return *this;
  }

  T& operator*() { return *val(); }

  const T& operator*() const { return *val(); }

  T* operator->() { return val(); }

  const T* operator->() const { return val(); }

 private:
  friend class MemoryManager;
  template <typename U>
  friend class managed_ptr;

  T* val() { return static_cast<T*>(val_); }
  const T* val() const { return static_cast<T*>(val_); }

  explicit managed_ptr(T* val) : managed_ptr_base(val) {}
};

template <typename T>
class ptr_accessor;

/**
 * Subclasses will have access to managed_ptrs to themselves after their
 * constructor returns.
 */
template <typename T>
class ManagedWithSelfPtr : public Managed {
 protected:
  const managed_ptr<T>& self() const { return *self_; }

 private:
  friend class MemoryManager;
  friend class ptr_accessor<T>;

  mutable std::unique_ptr<managed_ptr<T>> self_ = nullptr;
};

class PrivateBuffer {
 public:
  PrivateBuffer();
  ~PrivateBuffer();

  PrivateBuffer(PrivateBuffer&& o) noexcept;
  PrivateBuffer& operator=(PrivateBuffer&& o) noexcept;

  void* buf() const noexcept { return buf_; }
  std::size_t size() const noexcept { return size_; }

  /** Releases the buffer -- you must return it to the MemoryManager yourself
   * using `free_private_buffer`. */
  void* release() noexcept;

  friend void swap(PrivateBuffer& lhs, PrivateBuffer& rhs) noexcept {
    using std::swap;
    swap(lhs.buf_, rhs.buf_);
    swap(lhs.size_, rhs.size_);
  }

 private:
  friend class MemoryManager;

  void* buf_;
  std::size_t size_;

  PrivateBuffer(void* buf, std::size_t size) noexcept;

  PrivateBuffer(const PrivateBuffer&) = delete;
  PrivateBuffer& operator=(const PrivateBuffer&) = delete;
};

struct MemoryManagerStats {
  std::size_t allocated = 0;
  uint64_t num_objects = 0;
  uint64_t num_private_buffers = 0;
  uint64_t num_holds = 0;

  friend auto operator<=>(const MemoryManagerStats&,
                          const MemoryManagerStats&) = default;
};

std::ostream& operator<<(std::ostream& os, const MemoryManagerStats& stats);

/** The root of the object graph managed by a `MemoryManager`. */
class Root {
 public:
  virtual ~Root();

  virtual void visit_root(const ManagedVisitor& visitor) = 0;
};

/**
 * Controls when garbage collection occurs.
 *
 * Only called when the number of holds is zero, so some allocations may not be
 * visible to the policy.
 */
class GcPolicy {
 public:
  enum class Decision {
    DoNothing,
    FullGc,
  };

  virtual ~GcPolicy();

  virtual Decision on_object_allocation_request(
      const MemoryManagerStats& stats, std::size_t allocation_request) = 0;
  virtual Decision on_private_buffer_request(
      const MemoryManagerStats& stats, std::size_t allocation_request) = 0;
  virtual Decision on_hold_request(const MemoryManagerStats& stats) = 0;
};

/**
 * Does a full GC whenever it is legal to do so.
 *
 * This is good for stress testing your use of the `MemoryManager`,
 * particularly when used in conjunction with the address sanitizer,
 * which detects use-after-free. Its use is recommended when
 * developing new native libraries that interact with the memory
 * manager.
 */
class StressTestGcPolicy : public GcPolicy {
 public:
  Decision on_object_allocation_request(
      const MemoryManagerStats& stats, std::size_t allocation_request) override;
  Decision on_private_buffer_request(const MemoryManagerStats& stats,
                                     std::size_t allocation_request) override;
  Decision on_hold_request(const MemoryManagerStats& stats) override;
};

/** Allocates and manages memory for the emil runtime. */
class MemoryManager {
 public:
  explicit MemoryManager(Root& root);
  MemoryManager(Root& root, std::unique_ptr<GcPolicy> gc_policy);
  ~MemoryManager();

  using Stats = MemoryManagerStats;

  /**
   * Create a new managed object.
   *
   * If you will call `create` again before this object is reachable from a
   * root, be sure to take a `hold` by calling `acquire_hold`.
   */
  template <ManagedType T, class... Args>
  managed_ptr<T> create(Args&&... args);

  /**
   * Create a buffer that is owned by a managed object and whose
   * address is not shared and persisted.
   */
  [[nodiscard]] PrivateBuffer allocate_private_buffer(std::size_t size);

  /**
   * Returns a private buffer to the memory manager.
   *
   * This is normally called by `PrivateBuffer`'s destructor. Users should only
   * call this if they have taken ownership of the buffer by calling
   * `PrivateBuffer::release`.
   */
  void free_private_buffer(void* buf, std::size_t size);

  /** As long as this object lives, no garbage will be collected. */
  class hold {
   public:
    ~hold();
    hold(hold&& o);
    hold& operator=(hold&& o);

   private:
    friend class MemoryManager;
    MemoryManager* mgr_;
    explicit hold(MemoryManager* mgr);
    hold(const hold&) = delete;
    hold& operator=(const hold&) = delete;
  };

  [[nodiscard]] hold acquire_hold();

  Stats stats() const;

 private:
  friend class hold;

  Root& root_;
  std::unique_ptr<GcPolicy> gc_policy_;
  Managed* managed_ = nullptr;
  Stats stats_{};

  MemoryManager(const MemoryManager&) = delete;
  MemoryManager& operator=(const MemoryManager&) = delete;
  MemoryManager(MemoryManager&&) = delete;
  MemoryManager& operator=(MemoryManager&&) = delete;

  void free_obj(Managed* m);

  void enact_decision(GcPolicy::Decision decision);
  void full_gc();
};

template <ManagedType T, class... Args>
managed_ptr<T> make_managed(Args&&... args) {
  return ctx().mgr->create<T>(std::forward<Args>(args)...);
}

template <ManagedType T, class... Args>
managed_ptr<T> make_managed_from_tuple(std::tuple<Args...>&& args) {
  return std::apply(make_managed<T, Args...>, std::move(args));
}

template <ManagedType T, class... Args>
managed_ptr<T> MemoryManager::create(Args&&... args) {
  static_assert(sizeof(managed_ptr<T>) == sizeof(void*));

  const auto size = sizeof(T);
  if (stats_.num_holds == 0)
    enact_decision(gc_policy_->on_object_allocation_request(stats_, size));

  // No garbage collection allowed during construction of an object.
  hold h{this};
  stats_.allocated += size;
  ++stats_.num_objects;

  auto t = std::make_unique<T>(std::forward<Args>(args)...);
  assert(static_cast<Managed&>(*t).managed_size() == size);
  t->update_next_managed_and_clear(managed_);
  auto* tptr = t.release();
  managed_ = tptr;

  managed_ptr<T> ptr(tptr);
  if constexpr (detail::is_managed_with_self_ptr<T>) {
    static_cast<ManagedWithSelfPtr<T>*>(tptr)->self_ =
        std::make_unique<managed_ptr<T>>(ptr);
  }
  return ptr;
}

}  // namespace emil
