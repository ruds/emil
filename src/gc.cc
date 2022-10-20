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

#include <cassert>

namespace emil {

Managed::Managed() = default;
Managed::~Managed() = default;

managed_ptr_base::managed_ptr_base(Managed* val) noexcept : val_(val) {}
managed_ptr_base::~managed_ptr_base() = default;

void managed_ptr_base::visit(const ManagedVisitor& visitor) {
  visitor(*this);
  val_->visit_subobjects(visitor);
}

void managed_ptr_base::mark() { val_->is_marked = true; }

PrivateBuffer::~PrivateBuffer() {
  if (buf_) mgr_->free_private_buffer(buf_, size_);
}

PrivateBuffer::PrivateBuffer(MemoryManager* mgr, char* buf, std::size_t size)
    : mgr_(mgr), buf_(buf), size_(size) {}

PrivateBuffer::PrivateBuffer(PrivateBuffer&& o) noexcept
    : mgr_(o.mgr_), buf_(o.buf_), size_(o.size_) {
  o.buf_ = nullptr;
}

PrivateBuffer& PrivateBuffer::operator=(PrivateBuffer&& o) noexcept {
  if (&o == this) return *this;
  if (buf_) mgr_->free_private_buffer(buf_, size_);
  mgr_ = o.mgr_;
  buf_ = o.buf_;
  size_ = o.size_;
  o.buf_ = nullptr;
  return *this;
}

MemoryManager::MemoryManager() = default;

MemoryManager::~MemoryManager() {
  assert(stats_.num_holds == 0);
  Managed* next = managed_;
  while (next) {
    auto* t = next;
    next = t->next_managed;
    free_obj(t);
  }
}

PrivateBuffer MemoryManager::allocate_private_buffer(std::size_t size) {
  stats_.allocated += size;
  ++stats_.num_private_buffers;
  return PrivateBuffer(this, new char[size], size);
}

MemoryManager::hold::~hold() {
  if (mgr_) mgr_->release_hold();
}

MemoryManager::hold::hold(hold&& o) : mgr_(o.mgr_) { o.mgr_ = nullptr; }

MemoryManager::hold& MemoryManager::hold::operator=(hold&& o) {
  if (this != &o) {
    mgr_ = o.mgr_;
    o.mgr_ = nullptr;
  }
  return *this;
}

MemoryManager::hold::hold(MemoryManager* mgr) : mgr_(mgr) {}

MemoryManager::hold MemoryManager::acquire_hold() {
  ++stats_.num_holds;
  return {this};
}

MemoryManager::Stats MemoryManager::stats() const { return stats_; }

void MemoryManager::free_obj(Managed* m) {
  const auto size = m->size();
  assert(stats_.allocated >= size);
  stats_.allocated -= size;
  assert(stats_.num_objects != 0);
  --stats_.num_objects;
  delete m;
}

void MemoryManager::free_private_buffer(char* buf, std::size_t size) {
  assert(stats_.allocated >= size);
  stats_.allocated -= size;
  assert(stats_.num_private_buffers != 0);
  --stats_.num_private_buffers;
  delete[] buf;
}

void MemoryManager::release_hold() {
  assert(stats_.num_holds != 0);
  --stats_.num_holds;
}

}  // namespace emil
