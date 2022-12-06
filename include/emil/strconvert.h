// Copyright 2022 Matt Rudary

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <string>
#include <string_view>

namespace emil {

std::u8string to_u8string(std::string_view s);
void to_u8string(std::string_view s, std::u8string& out);

std::string to_hex(std::u8string_view s);
void to_hex(std::u8string_view s, std::string& out);

std::string to_std_string(std::u8string_view s);
void to_std_string(std::u8string_view s, std::string& out);

std::string to_std_string(std::u32string_view s);
void to_std_string(std::u32string_view s, std::string& out);

std::string to_std_string(char32_t c);
void to_std_string(char32_t c, std::string& out);

}  // namespace emil
