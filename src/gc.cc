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

#include <fmt/core.h>
#include <fmt/ostream.h>

#include <cassert>
#include <memory>

namespace emil {

ManagedVisitor::ManagedVisitor() = default;
ManagedVisitor::~ManagedVisitor() = default;

Managed::Managed() = default;
Managed::~Managed() = default;

bool Managed::mark() {
  bool was_marked = is_marked;
  is_marked = true;
  return !was_marked;
}

managed_ptr_base::managed_ptr_base(Managed* val) noexcept : val_(val) {}
managed_ptr_base::~managed_ptr_base() = default;

void managed_ptr_base::accept(const ManagedVisitor& visitor) {
  if (visitor.visit(*this)) val_->visit_subobjects(visitor);
}

bool managed_ptr_base::mark() { return val_->mark(); }

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

std::ostream& operator<<(std::ostream& os, const MemoryManagerStats& stats) {
  fmt::print(os,
             "MemoryManagerStats(allocated={}, num_objects={}, "
             "num_private_buffers={}, num_holds={})",
             stats.allocated, stats.num_objects, stats.num_private_buffers,
             stats.num_holds);
  return os;
}

Root::~Root() = default;

GcPolicy::~GcPolicy() = default;

StressTestGcPolicy::Decision StressTestGcPolicy::on_object_allocation_request(
    const MemoryManagerStats&, std::size_t) {
  return Decision::FullGc;
}

StressTestGcPolicy::Decision StressTestGcPolicy::on_private_buffer_request(
    const MemoryManagerStats&, std::size_t) {
  return Decision::FullGc;
}

StressTestGcPolicy::Decision StressTestGcPolicy::on_hold_request(
    const MemoryManagerStats&) {
  return Decision::FullGc;
}

MemoryManager::MemoryManager(Root& root)
    : MemoryManager(root, std::make_unique<StressTestGcPolicy>()) {}

MemoryManager::MemoryManager(Root& root, std::unique_ptr<GcPolicy> gc_policy)
    : root_(root), gc_policy_(std::move(gc_policy)) {}

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
  if (stats_.num_holds == 0)
    enact_decision(gc_policy_->on_private_buffer_request(stats_, size));
  stats_.allocated += size;
  ++stats_.num_private_buffers;
  return PrivateBuffer(this, new char[size], size);
}

MemoryManager::hold::~hold() {
  if (!mgr_) return;
  assert(mgr_->stats_.num_holds != 0);
  --mgr_->stats_.num_holds;
}

MemoryManager::hold::hold(hold&& o) : mgr_(o.mgr_) { o.mgr_ = nullptr; }

MemoryManager::hold& MemoryManager::hold::operator=(hold&& o) {
  if (this != &o) {
    mgr_ = o.mgr_;
    o.mgr_ = nullptr;
  }
  return *this;
}

MemoryManager::hold::hold(MemoryManager* mgr) : mgr_(mgr) {
  ++mgr_->stats_.num_holds;
}

MemoryManager::hold MemoryManager::acquire_hold() {
  if (stats_.num_holds == 0)
    enact_decision(gc_policy_->on_hold_request(stats_));
  return {this};
}

MemoryManager::Stats MemoryManager::stats() const { return stats_; }

void MemoryManager::free_obj(Managed* m) {
  const auto size = m->managed_size();
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

void MemoryManager::enact_decision(GcPolicy::Decision decision) {
  switch (decision) {
    case GcPolicy::Decision::DoNothing:
      return;

    case GcPolicy::Decision::FullGc:
      full_gc();
      return;
  }
}

class MarkVisitor : public ManagedVisitor {
  bool visit(managed_ptr_base& ptr) const override { return ptr.mark(); }
};

void MemoryManager::full_gc() {
  root_.visit_root(MarkVisitor());
  Managed** prev_next = &managed_;
  Managed* next = managed_;
  while (next) {
    if (next->is_marked) {
      next->is_marked = false;
      *prev_next = next;
      prev_next = &next->next_managed;
      next = next->next_managed;
    } else {
      Managed* to_delete = next;
      next = to_delete->next_managed;
      free_obj(to_delete);
    }
  }
  *prev_next = nullptr;
}

}  // namespace emil
