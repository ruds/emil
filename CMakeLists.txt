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

add_subdirectory(src)

if (EMIL_TESTS)
  add_subdirectory(test)
endif()
