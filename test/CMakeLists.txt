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

find_package(fmt REQUIRED)

option(EMIL_ACCEPTANCE_TESTS "Enable acceptance tests for Emil compiler" ON)

if (EMIL_ACCEPTANCE_TESTS)
  add_subdirectory(acceptance)
endif()

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/googletest" "extern/googletest")

mark_as_advanced(
  BUILD_GMOCK BUILD_GTEST BUILD_SHARED_LIBS
  gmock_build_tests gtest_build_samples gtest_build_tests
  gtest_disable_pthreads gtest_force_shared_crt gtest_hide_internal_symbols
)

set_target_properties(gtest PROPERTIES FOLDER extern)
set_target_properties(gtest_main PROPERTIES FOLDER extern)
set_target_properties(gmock PROPERTIES FOLDER extern)
set_target_properties(gmock_main PROPERTIES FOLDER extern)

add_library(test_util STATIC test_util.cc)
add_emil_options(test_util)
target_link_libraries(test_util PRIVATE runtime)

macro(emil_add_gtest TESTNAME FILES)
  set(LIBRARIES ${ARGN})
  add_executable(${TESTNAME} "${FILES}")
  add_emil_options(${TESTNAME})
  target_link_libraries(${TESTNAME} gtest gmock gtest_main test_util "${LIBRARIES}")
  gtest_discover_tests(${TESTNAME} PROPERTIES ENVIRONMENT
    "TEST_DATA_DIR=${PROJECT_SOURCE_DIR}/test/data")
  set_target_properties(${TESTNAME} PROPERTIES FOLDER test)
endmacro()

emil_add_gtest(bigint_test bigint_test.cc bigint util)
target_compile_options(bigint_test PRIVATE -Wno-overlength-strings)
emil_add_gtest(source_test source_test.cc lexer)
emil_add_gtest(text_input_test text_input_test.cc lexer)
emil_add_gtest(gc_test gc_test.cc runtime)
emil_add_gtest(string_test string_test.cc runtime util)
emil_add_gtest(collections_test collections_test.cc runtime)
emil_add_gtest(types_test types_test.cc runtime)
emil_add_gtest(processor_test processor_test.cc fmt::fmt)
target_include_directories(processor_test PRIVATE ../include)
