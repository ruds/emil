# Copyright 2022 Matt Rudary

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

add_golden_driver(parser-driver driver.cc)
target_link_libraries(parser-driver parser)

macro(parser_golden_test TESTNAME)
  add_golden_test(parser-driver "${TESTNAME}" VARIANT processor)
endmacro()

parser_golden_test(literal)
parser_golden_test(fstring)
parser_golden_test(identifier)
parser_golden_test(record)
parser_golden_test(paren)
parser_golden_test(list)
parser_golden_test(val)
parser_golden_test(let)
parser_golden_test(types)
parser_golden_test(fn)
parser_golden_test(if)
parser_golden_test(case)
parser_golden_test(operators)
parser_golden_test(application)
parser_golden_test(dtype)
