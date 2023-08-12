# Copyright 2023 Matt Rudary

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

find_package(fmt REQUIRED)

add_golden_driver(evaluator-driver driver.cc)
target_link_libraries(evaluator-driver interpreter runtime fmt::fmt)

macro(evaluator_golden_test TESTNAME)
  add_golden_test(evaluator-driver "${TESTNAME}")
endmacro()

evaluator_golden_test(empty)
evaluator_golden_test(literal)
