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

add_golden_driver(lexer-driver driver.cc)
target_link_libraries(lexer-driver lexer)

macro(lexer_golden_test TESTNAME)
  add_golden_test(lexer-driver "${TESTNAME}" VARIANT source)
  add_golden_test(lexer-driver "${TESTNAME}" VARIANT processor)
endmacro()

lexer_golden_test(iliteral)
lexer_golden_test(fpliteral)
lexer_golden_test(char)
lexer_golden_test(string)
lexer_golden_test(identifier)
lexer_golden_test(keywords)
lexer_golden_test(syntax)
lexer_golden_test(comment)
lexer_golden_test(fstring)
