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

add_executable(driver driver.cc)
add_emil_options(driver)
target_link_libraries(driver lexer)
target_compile_with_warnings(driver)
add_test(driver_build
  "${CMAKE_COMMAND}"
  --build "${CMAKE_BINARY_DIR}"
  --config $<CONFIG>
  --target driver
)
set_tests_properties(driver_build
  PROPERTIES FIXTURES_SETUP driver_fixture)

macro(lexer_golden_test TESTNAME)
  add_test(
    NAME "${TESTNAME}-create-output"
    COMMAND
    driver "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.in" "${TESTNAME}.out"
  )
  add_test(
    NAME "${TESTNAME}"
    COMMAND
    "${CMAKE_COMMAND}" -E compare_files
    "${TESTNAME}.out"
    "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.expected"
  )
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_REQUIRED driver_fixture)
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_SETUP "${TESTNAME}_fixture")
  set_tests_properties("${TESTNAME}"
    PROPERTIES FIXTURES_REQUIRED "${TESTNAME}_fixture")
endmacro()

lexer_golden_test(iliteral iliteral.in)
lexer_golden_test(fpliteral fpliteral.in)
lexer_golden_test(char char.in)
lexer_golden_test(string string.in)
lexer_golden_test(identifier identifier.in)
lexer_golden_test(keywords keywords.in)
lexer_golden_test(syntax syntax.in)
lexer_golden_test(comment comment.in)
lexer_golden_test(fstring fstring.in)
