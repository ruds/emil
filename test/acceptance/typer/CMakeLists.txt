# Copyright 2023 Matt Rudary

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

add_golden_driver(typer-driver driver.cc)
target_link_libraries(typer-driver typer fmt::fmt)

macro(typer_golden_test TESTNAME)
  add_golden_test(typer-driver "${TESTNAME}")
endmacro()

typer_golden_test(empty)
typer_golden_test(literal)
typer_golden_test(identifier)
typer_golden_test(record)
typer_golden_test(tuple)
typer_golden_test(sequenced)
typer_golden_test(list)
typer_golden_test(val)
typer_golden_test(let)
typer_golden_test(case)
typer_golden_test(fn)
typer_golden_test(application)
typer_golden_test(if)
typer_golden_test(dtype)
typer_golden_test(examples)
