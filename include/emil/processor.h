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

#include <coroutine>
#include <exception>
#include <stdexcept>
#include <utility>
#include <variant>

namespace emil::processor {

struct next_input {};
struct reset {};
struct eof {};

namespace detail {

template <typename... Ts>
struct overloaded : Ts... {
  using Ts::operator()...;
};

template <typename... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

}  // namespace detail

/**
 * A coroutine state object used to process streams.
 *
 * As a processor client, the idea is to provide one piece of input
 * data, read all output, and repeat. The stream can be reset if
 * necessary (e.g. because a lexing error requires that a
 * partially-parsed expression be abandoned). When the input stream is
 * complete, call `finish` and read any remaining output.
 *
 * Example usage:
 *  p = <get processor from coroutine factory>;
 *  while (event = pollEvent()) {
 *    if (event.type == CTRL_C) {
 *      p.reset();
 *    } else if (event.type == CTRL_D) {
 *      p.finish();
 *      while (p) doSomethingWith(p());
 *    } else {
 *      p.process(event.key);
 *      while (p) doSomethingWith(p());
 *    }
 *  }
 *
 * As a processor implementor, co_await on an instance of `next_input`
 * to get the next input; this will either return a value of type `In`
 * or throw `reset` or `eof` if `reset` or `finish` was called.
 *
 * Example usage:
 *  processor<char, std::string> partition_into_words() {
 *      std::string word;
 *      while (true) {
 *          char c;
 *          try {
 *              c = co_await next_input {};
 *          } catch (reset&) {
 *              word.clear();
 *              continue;
 *          } catch (eof&) {
 *              break;
 *          }
 *          if (std::isalpha(c)) {
 *              word.push_back(c);
 *          } else {
 *              if (!word.empty()) {
 *                  co_yield std::move(word);
 *                  word.clear();
 *              }
 *          }
 *      }
 *      if (!word.empty()) co_yield(std::move(word));
 *  }
 */
template <typename In, typename Out>
struct [[nodiscard]] processor {
  struct promise_type;
  using handle_type = std::coroutine_handle<promise_type>;

  /** Returns true if operator()() may be called. */
  explicit operator bool() const { return handle_.promise().ready(); }

  /**
   * Returns the next product of processing.
   *
   * Throws if the coroutine has thrown an unhandled exception.
   */
  Out operator()() {
    auto value = handle_.promise().get_value_or_throw();
    if (!handle_.done()) handle_.resume();
    return value;
  }

  void process(const In& in) {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    handle_.promise().provide_input(std::move(in));
    if (!handle_.done()) handle_.resume();
  }

  /** Provides data for processing. */
  void process(In&& in) {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    handle_.promise().provide_input(std::move(in));
    if (!handle_.done()) handle_.resume();
  }

  /** Discard any unprocessed data and start fresh. */
  void reset() {
    handle_.promise().reset();
    if (!handle_.done()) handle_.resume();
  }

  /** Signal that the input is complete. */
  void finish() {
    handle_.promise().finish();
    if (!handle_.done()) handle_.resume();
  }

  struct promise_type {
    std::variant<std::monostate, Out, std::exception_ptr> value;
    using input_type = std::variant<std::monostate, In, struct reset, eof>;
    input_type input;

    bool ready() const { return value.index() != 0; }

    Out get_value_or_throw() {
      return visit(
          detail::overloaded{
              [](std::monostate&&) -> Out {
                throw std::logic_error("Attempted to read when not ready.");
              },
              [this](Out&& out) {
                auto v = std::move(out);
                value = std::monostate{};
                return v;
              },
              [this](std::exception_ptr&& ptr) -> Out {
                auto p = std::move(ptr);
                value = std::monostate{};
                try {
                  std::rethrow_exception(p);
                } catch (struct reset) {
                  throw std::logic_error("Coroutine doesn't handle reset.");
                } catch (eof) {
                  throw std::logic_error("Coroutine doesn't handle finish.");
                }
              }},
          std::move(value));
    }

    void provide_input(In&& in) {
      if (input.index() != 0) {
        throw std::logic_error("Must read output before providing more input.");
      }
      input = std::move(in);
    }

    void provide_input(const In& in) {
      if (input.index() != 0) {
        throw std::logic_error("Must read output before providing more input.");
      }
      input = in;
    }

    void reset() {
      struct reset r;
      input = r;
      value = std::monostate{};
    }

    void finish() { input = eof{}; }

    std::suspend_always yield_value(Out&& v) {
      value = std::move(v);
      return {};
    }

    void return_void() {}

    void unhandled_exception() { value = std::current_exception(); }

    processor get_return_object() { return processor{this}; }

    std::suspend_always initial_suspend() { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }

    struct input_awaiter {
      input_type& input;

      bool await_ready() { return input.index() != 0; }
      void await_suspend(std::coroutine_handle<>) {}

      In await_resume() {
        return visit(
            detail::overloaded{[](std::monostate&&) -> In {
                                 throw std::logic_error(
                                     "Attempted to resume without input.");
                               },
                               [this](In&& in) -> In {
                                 auto v = std::move(in);
                                 input = std::monostate{};
                                 return v;
                               },
                               [this](struct reset r) -> In {
                                 input = std::monostate{};
                                 throw r;
                               },
                               [this](eof e) -> In {
                                 input = std::monostate{};
                                 throw e;
                               }},
            std::move(input));
      }
    };

    [[nodiscard]] input_awaiter await_transform(next_input) { return {input}; }
  };

  processor(const processor&) = delete;
  processor(processor&& o) : handle_(std::exchange(o.handle_, nullptr)) {}

  ~processor() {
    if (handle_) handle_.destroy();
  }

 private:
  friend struct promise_type;

  explicit processor(promise_type* p)
      : handle_(handle_type::from_promise(*p)) {}

  handle_type handle_;
};

}  // namespace emil::processor
