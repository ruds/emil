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

macro(add_golden_driver DRIVER SRCS)
  add_executable("${DRIVER}" "${SRCS}")
  add_emil_options("${DRIVER}")
  add_test("${DRIVER}_build"
    "${CMAKE_COMMAND}"
    --build "${CMAKE_BINARY_DIR}"
    --config $<CONFIG>
    --target "${DRIVER}"
  )
  set_tests_properties("${DRIVER}_build"
    PROPERTIES FIXTURES_SETUP "${DRIVER}_fixture")
endmacro()

macro(add_golden_test DRIVER TESTNAME)
  add_test(
    NAME "${TESTNAME}-create-output"
    COMMAND
    "${DRIVER}" "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.in" "${TESTNAME}.out"
  )
  add_test(
    NAME "${TESTNAME}"
    COMMAND
    "${CMAKE_COMMAND}" -E compare_files
    "${TESTNAME}.out"
    "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.expected"
  )
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_REQUIRED "${DRIVER}_fixture")
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_SETUP "${TESTNAME}_fixture")
  set_tests_properties("${TESTNAME}"
    PROPERTIES FIXTURES_REQUIRED "${TESTNAME}_fixture")
endmacro()

add_subdirectory(lexer)
add_subdirectory(parser)
