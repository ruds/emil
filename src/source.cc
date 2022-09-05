#include "emil/source.h"

#include <any>
#include <deque>
#include <istream>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <utility>

namespace emil {

using std::cbegin;
using std::cend;

namespace {
template <typename It>
class IteratorSource : public Source {
 public:
  IteratorSource(It begin, It end) : container_(), in_(begin), end_(end) {}
  template <typename T>
  explicit IteratorSource(T&& container)
      : container_(std::forward<T>(container)),
        in_(cbegin(any_cast<T&>(container_))),
        end_(cend(any_cast<T&>(container_))) {}
  ~IteratorSource() override = default;

  char32_t advance() override {
    if (empty(lookahead_buffer_)) {
      return *in_++;
    }
    char32_t c = lookahead_buffer_.front();
    lookahead_buffer_.pop_front();
    return c;
  }

  std::optional<char32_t> peek(size_t lookahead) override {
    while (size(lookahead_buffer_) <= lookahead && in_ != end_) {
      lookahead_buffer_.push_back(*in_++);
    }
    if (size(lookahead_buffer_) <= lookahead) {
      return {};
    }
    return lookahead_buffer_[lookahead];
  }

  bool at_end() const override {
    return empty(lookahead_buffer_) && in_ == end_;
  }

 private:
  std::any container_;
  It in_;
  It end_;
  std::deque<char32_t> lookahead_buffer_;
};
}  // namespace

std::unique_ptr<Source> make_source(std::basic_istream<char32_t>& in) {
  return std::make_unique<IteratorSource<std::istreambuf_iterator<char32_t>>>(
      std::istreambuf_iterator<char32_t>{in},
      std::istreambuf_iterator<char32_t>{});
}

std::unique_ptr<Source> make_source(std::u32string in) {
  return std::make_unique<IteratorSource<std::u32string::const_iterator>>(
      std::move(in));
}

}  // namespace emil
