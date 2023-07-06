// Copyright 2023 Matt Rudary

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#pragma once

#include <iostream>
#include <string>

#include "emil/processor.h"

namespace emil {

processor::processor<processor::unit, char32_t> read_stream(
    std::basic_istream<char32_t>& in);

processor::processor<processor::unit, char32_t> read_string(std::u32string in);

processor::processor_subtask<char32_t, std::u32string> next_grapheme_cluster();
processor::processor_subtask<char32_t, void> append_next_grapheme_cluster(
    std::u32string& out);

}  // namespace emil
