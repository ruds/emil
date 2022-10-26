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

#include "emil/runtime.h"

#include <cassert>
#include <stdexcept>

namespace emil {

namespace {
ContextManager* const CONTEXT_MANAGER = new ContextManager();
}

const RuntimeContext& ctx() {
  assert(CONTEXT_MANAGER->ctx_);
  return *CONTEXT_MANAGER->ctx_;
}

ContextManager* ContextManager::get() { return CONTEXT_MANAGER; }

void ContextManager::install_context(RuntimeContext& ctx) {
  if (ctx_) throw std::logic_error("Trying to replace a live context.");
  ctx_ = &ctx;
}

void ContextManager::uninstall_context() {
  if (!ctx_) throw std::logic_error("Trying to uninstall nonexistent context.");
  ctx_ = nullptr;
}

}  // namespace emil
