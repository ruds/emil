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
  virtual std::size_t size() const = 0;
};

template <typename T>
concept ManagedType = std::is_base_of<Managed, T>::value;

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

 protected:
  Managed* val_;

  explicit managed_ptr_base(Managed* val);

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
template <ManagedType T>
class managed_ptr : public managed_ptr_base {
 public:
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

    friend auto operator<=>(const Stats&, const Stats&) = default;
  };

  /** Create a new managed object. */
  template <ManagedType T, class... Args>
  managed_ptr<T> create(Args&&... args);

  /**
   * Create a buffer that is owned by a managed object and whose
   * address is not shared.
   */
  PrivateBuffer allocate_private_buffer(std::size_t size);

  Stats stats() const;

 private:
  friend class PrivateBuffer;

  Managed* managed_ = nullptr;
  Stats stats_{};

  MemoryManager(const MemoryManager&) = delete;
  MemoryManager& operator=(const MemoryManager&) = delete;
  MemoryManager(MemoryManager&&) = delete;
  MemoryManager& operator=(MemoryManager&&) = delete;

  void free_obj(Managed* m);
  void free_private_buffer(char* buf, std::size_t size);
};

template <ManagedType T, class... Args>
managed_ptr<T> MemoryManager::create(Args&&... args) {
  const auto size = sizeof(T);
  stats_.allocated += size;
  ++stats_.num_objects;
  T* t = new T(std::forward<Args>(args)...);
  assert(static_cast<Managed*>(t)->size() == size);
  t->next_managed = managed_;
  managed_ = t;
  return managed_ptr<T>(t);
}

}  // namespace emil
