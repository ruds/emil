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
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

namespace emil {

class MemoryManager;
class managed_ptr_base;

using ManagedVisitor = std::function<void(managed_ptr_base&)>;

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

  Managed* next_managed = nullptr;
  bool is_marked = false;

  Managed(const Managed&) = delete;
  Managed& operator=(const Managed&) = delete;

  /**
   * Visits all the managed subobjects of this object.
   *
   * Implementations should pass the visitor to the visit method of
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
};

template <typename T>
class ManagedWithSelfPtr;

namespace detail {

template <typename T>
void is_managed_with_self_ptr_impl(const ManagedWithSelfPtr<T>&);

template <typename T>
concept is_managed_with_self_ptr = requires(const T& t) {
  is_managed_with_self_ptr_impl<T>(t);
};
}  // namespace detail

template <typename T>
concept ManagedType =
    std::is_base_of<Managed, T>::value || detail::is_managed_with_self_ptr<T>;

template <typename T, typename U>
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
  virtual ~managed_ptr_base();
  Managed& operator*() { return *val_; }
  const Managed& operator*() const { return *val_; }
  Managed* operator->() { return val_; }
  const Managed* operator->() const { return val_; }

  void visit(const ManagedVisitor& visitor);

  explicit operator bool() const noexcept { return val_; }

  friend bool operator==(const managed_ptr_base& l, const managed_ptr_base& r) {
    return l.val_ == r.val_;
  }

 protected:
  Managed* val_;

  explicit managed_ptr_base(Managed* val) noexcept;

 private:
  friend class MemoryManager;

  void mark();
};

/**
 * A pointer to a managed object.
 *
 * Users of this interface must not capture the address of the managed
 * object in a way that may outlive the lifetime of the managed_ptr.
 */
template <typename T>
class managed_ptr : public managed_ptr_base {
 public:
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

  ~managed_ptr() override = default;

  T& operator*() { return *val(); }

  const T& operator*() const { return *val(); }

  T* operator->() { return val(); }

  const T* operator->() const { return val(); }

 private:
  friend class MemoryManager;

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
  ~PrivateBuffer();

  char* buf() const { return buf_; }
  std::size_t size() const { return size_; }

  friend void swap(PrivateBuffer& lhs, PrivateBuffer& rhs) {
    using std::swap;
    swap(lhs.mgr_, rhs.mgr_);
    swap(lhs.buf_, rhs.buf_);
    swap(lhs.size_, rhs.size_);
  }

 private:
  friend class MemoryManager;

  MemoryManager* mgr_;
  char* buf_;
  std::size_t size_;

  PrivateBuffer(MemoryManager* mgr, char* buf, std::size_t size);

  PrivateBuffer(const PrivateBuffer&) = delete;
  PrivateBuffer& operator=(const PrivateBuffer&) = delete;

  PrivateBuffer(PrivateBuffer&& o) noexcept;
  PrivateBuffer& operator=(PrivateBuffer&& o) noexcept;
};

/** Allocates and manages memory for the emil runtime. */
class MemoryManager {
 public:
  MemoryManager();
  ~MemoryManager();

  struct Stats {
    std::size_t allocated = 0;
    uint64_t num_objects = 0;
    uint64_t num_private_buffers = 0;
    uint64_t num_holds = 0;

    friend auto operator<=>(const Stats&, const Stats&) = default;
  };

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
  PrivateBuffer allocate_private_buffer(std::size_t size);

  /** As long as this object lives, no garbage will be collected. */
  class hold {
   public:
    ~hold();
    hold(hold&& o);
    hold& operator=(hold&& o);

   private:
    friend class MemoryManager;
    MemoryManager* mgr_;
    hold(MemoryManager* mgr);
    hold(const hold&) = delete;
    hold& operator=(const hold&) = delete;
  };

  hold acquire_hold();

  Stats stats() const;

 private:
  friend class PrivateBuffer;
  friend class hold;

  Managed* managed_ = nullptr;
  Stats stats_{};

  MemoryManager(const MemoryManager&) = delete;
  MemoryManager& operator=(const MemoryManager&) = delete;
  MemoryManager(MemoryManager&&) = delete;
  MemoryManager& operator=(MemoryManager&&) = delete;

  void free_obj(Managed* m);
  void free_private_buffer(char* buf, std::size_t size);
  void release_hold();
};

template <ManagedType T, class... Args>
managed_ptr<T> MemoryManager::create(Args&&... args) {
  const auto size = sizeof(T);
  stats_.allocated += size;
  ++stats_.num_objects;
  // cppcheck-suppress cppcheckError
  T* t = new T(std::forward<Args>(args)...);
  assert(static_cast<Managed*>(t)->managed_size() == size);
  t->next_managed = managed_;
  managed_ = t;
  managed_ptr<T> ptr(t);
  if constexpr (detail::is_managed_with_self_ptr<T>) {
    static_cast<ManagedWithSelfPtr<T>*>(t)->self_ =
        std::make_unique<managed_ptr<T>>(ptr);
  }
  return ptr;
}

}  // namespace emil
