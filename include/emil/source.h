#pragma once

#include <istream>
#include <memory>
#include <optional>
#include <string>

namespace emil {

class Source {
 public:
  virtual ~Source() = default;
  virtual char32_t advance() = 0;
  virtual std::optional<char32_t> peek(size_t lookahead = 0) = 0;
  virtual bool at_end() const = 0;
};

std::unique_ptr<Source> make_source(std::basic_istream<char32_t>& in);
std::unique_ptr<Source> make_source(std::u32string in);

}  // namespace emil
