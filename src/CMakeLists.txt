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

find_package(ICU COMPONENTS uc i18n data REQUIRED)
find_package(fmt REQUIRED)
find_package(Python3 COMPONENTS Interpreter REQUIRED)

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/utfcpp" "extern/utfcpp")
add_subdirectory("${PROJECT_SOURCE_DIR}/extern/cpp-linenoise" "extern/cpp-linenoise")

add_custom_command(
  OUTPUT
  "${CMAKE_CURRENT_BINARY_DIR}/private-includes/private/power_tables.h"
  COMMAND
  "${Python3_EXECUTABLE}"
  ../tools/genpowtab.py
  "${CMAKE_CURRENT_BINARY_DIR}/private-includes/private/power_tables.h"
  DEPENDS ../tools/genpowtab.py
)

add_library(bigint STATIC bigint.cc)
add_emil_options(bigint)
target_include_directories(bigint
  PUBLIC ../include
  PRIVATE "${CMAKE_CURRENT_BINARY_DIR}/private-includes")
target_sources(bigint
  PRIVATE "${CMAKE_CURRENT_BINARY_DIR}/private-includes/private/power_tables.h")
target_link_libraries(bigint PRIVATE fmt::fmt)

add_library(util STATIC strconvert.cc)
add_emil_options(util)
target_include_directories(util PUBLIC ../include)
target_link_libraries(util PRIVATE fmt::fmt utf8cpp)

add_library(lexer STATIC lexer.cc source.cc text_input.cc)
add_emil_options(lexer)
target_include_directories(lexer
  PUBLIC ../include
  PRIVATE ./private-includes)
target_link_libraries(lexer
  PUBLIC fmt::fmt utf8cpp ICU::uc ICU::data
  PRIVATE util)

add_custom_command(
  OUTPUT
  "${CMAKE_CURRENT_BINARY_DIR}/include/emil/ast.h"
  "${CMAKE_CURRENT_BINARY_DIR}/ast.cc"
  COMMAND
  genast
  "${CMAKE_CURRENT_BINARY_DIR}/include/emil/ast.h"
  "${CMAKE_CURRENT_BINARY_DIR}/ast.cc"
  DEPENDS genast
)

add_library(ast STATIC "${CMAKE_CURRENT_BINARY_DIR}/ast.cc" ast_printer.cc)
add_emil_options(ast)
target_link_libraries(ast PUBLIC fmt::fmt)
target_include_directories(ast
  PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/include" ../include
  PRIVATE ./private-includes)

add_library(parser STATIC parser.cc)
add_emil_options(parser)
target_link_libraries(parser PUBLIC ast lexer)
target_include_directories(parser PUBLIC ../include)

add_library(runtime STATIC gc.cc reporter.cc runtime.cc string.cc types.cc)
add_emil_options(runtime)
target_include_directories(runtime
  PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/include" ../include)
target_link_libraries(runtime PUBLIC util fmt::fmt PRIVATE utf8cpp)

add_library(typed_ast STATIC typed_ast.cc)
add_emil_options(typed_ast)
target_link_libraries(typed_ast PUBLIC bigint runtime fmt::fmt)
target_include_directories(typed_ast PUBLIC ../include)

add_library(typer STATIC typer.cc typed_ast.cc)
add_emil_options(typer)
target_include_directories(typer PUBLIC ../include)
target_link_libraries(typer
  PUBLIC ast typed_ast runtime
  PRIVATE parser)

add_executable(repl repl.cc)
add_emil_options(repl)
target_link_libraries(repl linenoise fmt::fmt)
