cmake_minimum_required(VERSION 3.24)

project(
  Emil
  VERSION 0.1
  DESCRIPTION "The Emil programming language"
  LANGUAGES CXX
)

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
      target_compile_options("${TARGET}" PRIVATE -Wall -Wextra -Wpedantic -Werror)
    endif()
  endif()
endmacro()

find_program(IWYU_PATH NAMES include-what-you-use iwyu REQUIRED)
set(IWYU "${IWYU_PATH}" -Xiwyu --error
  -Xiwyu "--mapping_file=${CMAKE_CURRENT_LIST_DIR}/iwyu.imp")

find_program(CLANG_TIDY NAMES clang-tidy REQUIRED)

macro(add_emil_options TARGET)
  target_compile_features("${TARGET}" PUBLIC cxx_std_23)
  target_compile_with_warnings("${TARGET}")
  set_property(TARGET "${TARGET}" PROPERTY CXX_INCLUDE_WHAT_YOU_USE "${IWYU}")
  set_property(TARGET "${TARGET}" PROPERTY CXX_CLANG_TIDY "${CLANG_TIDY}")
endmacro()

add_subdirectory(src)

if (EMIL_TESTS)
  add_subdirectory(test)
endif()
