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

#include "emil/runtime.h"

namespace emil {

ManagedVisitor::ManagedVisitor() = default;
ManagedVisitor::~ManagedVisitor() = default;

Managed::Managed() = default;
Managed::~Managed() = default;

namespace {
static_assert(alignof(Managed) >= 2);
constexpr std::uintptr_t TAG_MASK = 1;
constexpr std::uintptr_t PTR_MASK = ~TAG_MASK;
}  // namespace

bool Managed::mark() {
  bool was_marked = is_marked();
  next_managed_ |= TAG_MASK;
  return !was_marked;
}

void Managed::update_next_managed_and_clear(Managed* next) {
  next_managed_ = reinterpret_cast<std::uintptr_t>(next);
  assert(!is_marked());
}

bool Managed::is_marked() const { return next_managed_ & TAG_MASK; }

Managed* Managed::next_managed() const {
  return reinterpret_cast<Managed*>(next_managed_ & PTR_MASK);
}

managed_ptr_base::managed_ptr_base(Managed* val) noexcept : val_(val) {}
managed_ptr_base::~managed_ptr_base() = default;

void managed_ptr_base::accept(const ManagedVisitor& visitor) {
  if (visitor.visit(*this)) val_->visit_subobjects(visitor);
}

bool managed_ptr_base::mark() { return val_->mark(); }

PrivateBuffer::PrivateBuffer() : buf_(nullptr), size_(0) {}

PrivateBuffer::~PrivateBuffer() {
  if (buf_) ctx().mgr->free_private_buffer(buf_, size_);
}

PrivateBuffer::PrivateBuffer(void* buf, std::size_t size) noexcept
    : buf_(buf), size_(size) {}

PrivateBuffer::PrivateBuffer(PrivateBuffer&& o) noexcept
    : buf_(o.buf_), size_(o.size_) {
  o.buf_ = nullptr;
}

PrivateBuffer& PrivateBuffer::operator=(PrivateBuffer&& o) noexcept {
  if (&o == this) return *this;
  if (buf_) ctx().mgr->free_private_buffer(buf_, size_);
  buf_ = o.buf_;
  size_ = o.size_;
  o.buf_ = nullptr;
  return *this;
}

void* PrivateBuffer::release() noexcept {
  void* p = buf_;
  buf_ = nullptr;
  return p;
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
    next = t->next_managed();
    free_obj(t);
  }
}

PrivateBuffer MemoryManager::allocate_private_buffer(std::size_t size) {
  if (stats_.num_holds == 0)
    enact_decision(gc_policy_->on_private_buffer_request(stats_, size));
  stats_.allocated += size;
  ++stats_.num_private_buffers;
  return PrivateBuffer(operator new(size), size);
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

void MemoryManager::free_private_buffer(void* buf, std::size_t size) {
  assert(stats_.allocated >= size);
  stats_.allocated -= size;
  assert(stats_.num_private_buffers != 0);
  --stats_.num_private_buffers;
  operator delete(buf);
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
  Managed* prev = nullptr;
  Managed* next = managed_;
  while (next) {
    if (next->is_marked()) {
      if (prev) {
        prev->update_next_managed_and_clear(next);
      } else {
        managed_ = next;
      }
      prev = next;
      next = next->next_managed();
    } else {
      Managed* to_delete = next;
      next = to_delete->next_managed();
      free_obj(to_delete);
    }
  }
  if (prev) {
    prev->update_next_managed_and_clear(nullptr);
  } else {
    managed_ = nullptr;
  }
}

}  // namespace emil
