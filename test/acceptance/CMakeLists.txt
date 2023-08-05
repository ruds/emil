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
  cmake_parse_arguments(GOLDEN_TEST "" "VARIANT" "" ${ARGN})
  if(DEFINED GOLDEN_TEST_UNPARSED_ARGUMENTS)
    message(FATAL_ERROR
      "Unparsed arguments ${GOLDEN_TEST_UNPARSED_ARGUMENTS}")
  endif()

  set(GOLDEN_TEST_CMD "${DRIVER}")
  if(DEFINED GOLDEN_TEST_VARIANT)
    list(APPEND GOLDEN_TEST_CMD "${GOLDEN_TEST_VARIANT}")
    set(BASENAME "${DRIVER}-${GOLDEN_TEST_VARIANT}")
    set(OUTFILENAME "${TESTNAME}-${GOLDEN_TEST_VARIANT}")
  else()
    set(BASENAME "${DRIVER}")
    set(OUTFILENAME "${TESTNAME}")
  endif()
  list(APPEND GOLDEN_TEST_CMD
    "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.in"
    "${CMAKE_CURRENT_BINARY_DIR}/${OUTFILENAME}.out"
  )

  add_test(
    NAME "${BASENAME} ${TESTNAME}-create-output"
    COMMAND
    "${GOLDEN_TEST_CMD}"
    COMMAND_EXPAND_LISTS
  )
  add_test(
    NAME "${BASENAME} ${TESTNAME}"
    COMMAND
    "${CMAKE_COMMAND}" -E compare_files
    "${CMAKE_CURRENT_BINARY_DIR}/${OUTFILENAME}.out"
    "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.expected"
  )

  set_tests_properties(
    "${BASENAME} ${TESTNAME}-create-output"
    PROPERTIES
    FIXTURES_REQUIRED "${DRIVER}_fixture")
  set_tests_properties(
    "${BASENAME} ${TESTNAME}-create-output"
    PROPERTIES
    FIXTURES_SETUP "${BASENAME}_${TESTNAME}_fixture")
  set_tests_properties(
    "${BASENAME} ${TESTNAME}"
    PROPERTIES
    FIXTURES_REQUIRED "${BASENAME}_${TESTNAME}_fixture")
endmacro()

add_subdirectory(lexer)
add_subdirectory(parser)
add_subdirectory(typer)
