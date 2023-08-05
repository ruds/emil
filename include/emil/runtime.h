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

namespace emil {

class MemoryManager;

namespace testing {
class DriverContextAccessor;
class TestContextHolder;
}  // namespace testing

/** Important context that must be available at runtime. */
struct RuntimeContext {
  MemoryManager* mgr;
};

/** Get the shared context. */
const RuntimeContext& ctx();

/** Manages the shared context -- limited access interface. */
class ContextManager {
  friend class InterpreterImpl;
  friend class Runtime;
  friend class testing::DriverContextAccessor;
  friend class testing::TestContextHolder;
  friend const RuntimeContext& ctx();

  static ContextManager* get();

  RuntimeContext* ctx_ = nullptr;

  void install_context(RuntimeContext& ctx);
  void uninstall_context();
};

}  // namespace emil
