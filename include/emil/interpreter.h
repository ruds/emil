// Copyright 2023 Matt Rudary

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

#include <memory>
#include <string>

namespace emil {

class InterpreterImpl;
class Reporter;

class Interpreter {
 public:
  explicit Interpreter(Reporter& reporter);
  ~Interpreter();

  /**
   * Process a line of input.
   *
   * Returns true if more input is required to complete a top-level
   * declaration (i.e. if the previous input produced a partial
   * declaration).
   */
  bool process_line(std::string line);

 private:
  std::unique_ptr<InterpreterImpl> impl_;
};

}  // namespace emil
