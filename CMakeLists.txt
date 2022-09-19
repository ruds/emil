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

cmake_minimum_required(VERSION 3.24)

project(
  Emil
  VERSION 0.1
  DESCRIPTION "The Emil programming language"
  LANGUAGES CXX
)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/cmake")

if (PROJECT_SOURCE_DIR STREQUAL PROJECT_BINARY_DIR)
  message(
    FATAL_ERROR
    "In-source builds are forbidden. Please create a build directory and run from there."
  )
endif()

if (CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME)
  set(IS_ROOT_PROJECT ON)
  set(CMAKE_CXX_EXTENSIONS OFF)

  set_property(GLOBAL PROPERTY USE_FOLDERS ON)

  include(CTest)
else()
  set(IS_ROOT_PROJECT OFF)
endif()

option(EMIL_TESTS "Enable tests for Emil" ${IS_ROOT_PROJECT})
option(EMIL_WARNINGS "Compile with lots of warnings" ${IS_ROOT_PROJECT})

macro(target_compile_with_warnings TARGET)
  if (EMIL_WARNINGS)
    if (MSVC)
      target_compile_options("${TARGET}" PRIVATE /W4 /WX)
    else()
      target_compile_options("${TARGET}" PRIVATE
        -Wall -Wextra -Wpedantic -Werror -Wimplicit-fallthrough)
    endif()
  endif()
endmacro()

find_program(IWYU_PATH NAMES include-what-you-use iwyu)
if (IWYU_PATH)
  set(IWYU_DEFAULT "${IWYU_PATH}" -Xiwyu --error
    -Xiwyu "--mapping_file=${CMAKE_CURRENT_LIST_DIR}/iwyu.imp")
else()
  set(IWYU_DEFAULT "")
endif()
set(IWYU "${IWYU_DEFAULT}" CACHE STRING "The IWYU command line")

find_program(CLANG_TIDY_DEFAULT NAMES clang-tidy)
set(CLANG_TIDY "${CLANG_TIDY_DEFAULT}"
  CACHE STRING "The clang-tidy command line")

find_program(CPPCHECK_PATH NAMES cppcheck)
if (CPPCHECK_PATH)
  set(CPPCHECK_DEFAULT "${CPPCHECK_PATH}" --enable=style
    --inconclusive --inline-suppr --library=googletest
    "--suppressions-list=${CMAKE_CURRENT_LIST_DIR}/.cppcheck-suppressions")
else()
  set(CPPCHECK_DEFAULT "")
endif()
set(CPPCHECK "${CPPCHECK_DEFAULT}"
  CACHE STRING "The cppcheck command line")

find_program(CPPLINT_DEFAULT NAMES cpplint)
set(CPPLINT "${CPPLINT_DEFAULT}"
  CACHE STRING "The cpplint command line")

set(SANITIZER_CHOICES none address leak thread undefined memory)
set(SANITIZER none CACHE STRING "Which sanitizer to build with")
set_property(CACHE SANITIZER PROPERTY STRINGS "${SANITIZER_CHOICES}")

if(NOT SANITIZER IN_LIST SANITIZER_CHOICES)
  message(FATAL_ERROR "SANITIZER must be one of ${SANITIZER_CHOICES}")
endif()

macro(add_emil_options TARGET)
  target_compile_features("${TARGET}" PUBLIC cxx_std_23)
  target_compile_with_warnings("${TARGET}")
  if (IWYU)
    set_property(TARGET "${TARGET}" PROPERTY CXX_INCLUDE_WHAT_YOU_USE "${IWYU}")
  endif()
  if (CLANG_TIDY)
    set_property(TARGET "${TARGET}" PROPERTY CXX_CLANG_TIDY "${CLANG_TIDY}")
  endif()
  if (CPPCHECK)
    set_property(TARGET "${TARGET}" PROPERTY CXX_CPPCHECK "${CPPCHECK}")
  endif()
  if (CPPLINT)
    set_property(TARGET "${TARGET}" PROPERTY CXX_CPPLINT "${CPPLINT}")
  endif()
endmacro()

add_subdirectory(tools)
add_subdirectory(src)

if (EMIL_TESTS)
  enable_testing()
  include(GoogleTest)
  add_subdirectory(test)
endif()
