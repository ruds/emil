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
find_package(GMPXX REQUIRED)

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/utfcpp" "extern/utfcpp")

add_library(lexer STATIC lexer.cc source.cc strconvert.cc)
add_emil_options(lexer)
target_include_directories(lexer PUBLIC ../include "${GMPXX_INCLUDE_DIRS}")
target_include_directories(lexer PRIVATE ./private)
target_link_libraries(lexer PUBLIC
  fmt::fmt utf8cpp ICU::uc ICU::data "${GMPXX_LIBRARIES}")

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

add_library(parser STATIC
  parser.cc ast_printer.cc "${CMAKE_CURRENT_BINARY_DIR}/ast.cc")
add_emil_options(parser)
target_link_libraries(parser PUBLIC lexer)
target_include_directories(parser
  PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/include" ../include)
target_include_directories(parser PRIVATE .)
