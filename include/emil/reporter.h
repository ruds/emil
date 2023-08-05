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

#include <string_view>

namespace emil {

class Expr;
struct Location;

namespace typing {
class Type;
class TypeScheme;
}  // namespace typing

class Reporter {
 public:
  virtual ~Reporter();

  virtual void report_error(const Location& location,
                            std::string_view text) = 0;
  virtual void report_warning(const Location& location,
                              std::string_view text) = 0;
  /**
   * This should be used to report information to the user.
   *
   * Examples: type judgments and values of variables bound by a declaration.
   */
  virtual void report_info(std::string_view text) = 0;
  virtual void report_type_judgement(const Location& location, const Expr& expr,
                                     const typing::Type& type) = 0;
  virtual void report_type_judgement(const Location& location,
                                     std::string_view id,
                                     const typing::TypeScheme& sigma) = 0;
};

}  // namespace emil
