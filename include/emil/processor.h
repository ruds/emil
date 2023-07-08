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

#include <cassert>
#include <concepts>
#include <coroutine>
#include <cstddef>
#include <deque>
#include <exception>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

namespace emil::processor {

/** Marker class used by coroutines returning `processor` or
 * `processor_subtask` to request the next input item. */
struct next_input {};
/** Marker class used by coroutines returning `processor` or
 * `processor_subtask` to request a preview of the `i`th future input item. */
struct peek {
  std::size_t i = 1;
};
/** Thrown within coroutine bodies when the input stream has signaled a reset.
 */
struct reset {};
/** Thrown within coroutine bodies when the input stream has been exhausted. */
struct eof {};
/** A type with a single value. Used as input to create a processor
 * that's really a generator. */
struct unit {};

namespace detail {

template <typename... Ts>
struct overloaded : Ts... {
  using Ts::operator()...;
};

template <typename... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

/** Used to track the execution stack of `processor_subtask`s. */
struct processor_stack_frame {
  std::coroutine_handle<> handle;
  processor_stack_frame* inner = nullptr;
  /** If nonzero, a request to peek ahead the given number of inputs. */
  std::size_t peek_request = 0;

  explicit processor_stack_frame(std::coroutine_handle<> h) : handle(h) {}

  /**
   * Resumes execution of a stack frame, returning true if the frame is
   * complete.
   *
   * If the frame has an inner frame that is not complete, resume that first,
   * only resuming the coroutine at this level if the inner frame completes.
   */
  bool resume() {
    if (!handle || handle.done()) return true;
    if (!inner || inner->resume()) {
      handle.resume();
      return handle.done();
    }
    return false;
  }
};

/** Type traits for the input type for a processor/processor_subtask. */
template <typename In>
struct input_traits {
  using peek_type = const In*;
  using input_type = const In&;

  static peek_type from_pointer(const In* in) { return in; }
};

template <typename T>
concept scalar = std::is_scalar_v<T>;

template <scalar In>
struct input_traits<In> {
  using peek_type = std::optional<In>;
  using input_type = In;

  static peek_type from_pointer(const In* in) {
    return in ? std::make_optional(*in) : std::nullopt;
  }
};

/** Interface that allows promises to interact with the processor input. */
template <typename In>
struct InputInterface {
  virtual ~InputInterface() = default;
  /** May throw eof or reset. */
  virtual In get_input() = 0;
  /** May throw reset. */
  virtual typename input_traits<In>::peek_type peek(std::size_t i) = 0;
  /**
   * Determines whether the requested input has already been read.
   *
   * When i == 0, the requested input is the result of `co_await next_input{}`.
   * Otherwise, it is `co_await peek{i};`
   */
  virtual bool input_ready(std::size_t i) const = 0;
  /** When true, no more input is available. */
  virtual bool input_complete() const = 0;
  /** If nonzero, a request to peek ahead the given number of inputs. */
  virtual void set_peek_request(std::size_t peek_request) = 0;
};

template <typename In>
using InputInterfaceCallback =
    std::function<std::shared_ptr<InputInterface<In>>()>;

template <typename In>
std::shared_ptr<InputInterface<In>> input_interface(
    std::shared_ptr<InputInterface<In>>&& in) {
  return std::move(in);
}

template <typename RequestedIn, typename AvailableIn>
struct DelegatingInputInterface : public InputInterface<RequestedIn> {
  explicit DelegatingInputInterface(
      std::shared_ptr<InputInterface<AvailableIn>>&& delegate)
      : delegate_(std::move(delegate)) {}

  RequestedIn get_input() override { return delegate_->get_input(); }

  typename input_traits<RequestedIn>::peek_type peek(std::size_t i) override {
    return delegate_->peek(i);
  }

  bool input_ready(std::size_t i) const override {
    return delegate_->input_ready(i);
  }

  bool input_complete() const override { return delegate_->input_complete(); }

  void set_peek_request(std::size_t peek_request) override {
    delegate_->set_peek_request(peek_request);
  }

 private:
  std::shared_ptr<InputInterface<AvailableIn>> delegate_;
};

template <typename RequestedIn, typename AvailableIn>
std::shared_ptr<InputInterface<RequestedIn>> input_interface(
    std::shared_ptr<InputInterface<AvailableIn>>&& in)
  requires(!std::is_same_v<RequestedIn, AvailableIn>)
{
  return std::make_shared<DelegatingInputInterface<RequestedIn, AvailableIn>>(
      std::move(in));
}

template <typename P>
concept Promise = requires(P p) {
  typename P::input_type;
  p.get_value_or_throw();
  { p.get_stack_frame() } -> std::same_as<processor_stack_frame*>;
  { p.output_ready() } -> std::convertible_to<bool>;
  {
    p.input_interface()
  } -> std::same_as<std::shared_ptr<InputInterface<typename P::input_type>>>;
};

template <typename P>
concept InnerPromise = requires(P p) {
  typename P::input_type;
  p.set_input_interface_callback(
      std::declval<InputInterfaceCallback<typename P::input_type>>());
};

/** Manages the execution of `co_await processor_subtask`. */
template <typename P>
struct subtask_awaiter {
  explicit subtask_awaiter(std::coroutine_handle<P> h) : handle_(h) {}
  ~subtask_awaiter();

  // We're considering suspending the task for one of two reasons.
  // Either the task has completed, or it has stopped to ask for
  // input. If it's completed, we don't actually need to suspend it
  // and we're ready to resume immediately.
  constexpr bool await_ready() const noexcept {
    assert(handle_);
    return handle_.done();
  }

  template <Promise P2>
  void await_suspend(std::coroutine_handle<P2> caller) {
    assert(handle_);
    // Link the frame of the calling coroutine to the frame of the
    // coroutine being suspended. That will allow us to resume the inner
    // coroutine later.
    auto* outer_frame = caller.promise().get_stack_frame();
    auto* inner_frame = handle_.promise().get_stack_frame();
    outer_frame->inner = inner_frame;
    outer_frame->peek_request = inner_frame->peek_request;
    // When we resume later, we'll need to read the input from the
    // root of the call tree. We don't have direct access to it, so we
    // need to call up the chain after each intervening level has been
    // linked in this way.
    handle_.promise().set_input_interface_callback([caller]() {
      assert(caller);
      return input_interface<typename P::input_type>(
          caller.promise().input_interface());
    });
    auto input = caller.promise().input_interface();
    if (input) {
      // If there's already input available, we can resume immediately.
      if (input->input_ready(inner_frame->peek_request)) {
        outer_frame->resume();
      } else {
        input->set_peek_request(inner_frame->peek_request);
      }
    }
  }

  // Returns the `co_return`ed value and unlinks the inner frame.
  auto await_resume() {
    assert(handle_);
    assert(handle_.promise().output_ready());
    return handle_.promise().get_value_or_throw();
  }

 private:
  std::coroutine_handle<P> handle_;
};

template <typename P>
subtask_awaiter<P>::~subtask_awaiter() {
  static_assert(Promise<P> && InnerPromise<P>);
}

/** Manages the execution of `co_await next_input{}`. */
template <typename P>
struct input_awaiter {
  explicit input_awaiter(std::coroutine_handle<P> h) : h_(h) {}
  ~input_awaiter();

  bool await_ready() {
    assert(h_);
    auto input = h_.promise().input_interface();
    // If we already know the next input, no need to suspend.
    return input && input->input_ready(0);
  }

  void await_suspend(std::coroutine_handle<P> h) {
    h_ = h;
    h_.promise().get_stack_frame()->peek_request = 0;
    auto input = h_.promise().input_interface();
    if (input) input->set_peek_request(0);
  }

  auto await_resume() {
    auto input = h_.promise().input_interface();
    return input->get_input();
  }

 private:
  std::coroutine_handle<P> h_;
};

template <typename P>
input_awaiter<P>::~input_awaiter() {
  static_assert(Promise<P>);
}

/** Manages the execution of `co_await peek_input{i}`. */
template <typename P>
struct peek_awaiter {
  peek_awaiter(std::coroutine_handle<P> h, std::size_t request)
      : h_(h), request_(request) {
    if (request == 0)
      throw std::invalid_argument("Must peek a non-zero number");
  }
  ~peek_awaiter();

  bool await_ready() {
    assert(h_);
    auto input = h_.promise().input_interface();
    // If we already know the next input, no need to suspend.
    return input && input->input_ready(request_);
  }

  void await_suspend(std::coroutine_handle<P> h) {
    h_ = h;
    h_.promise().get_stack_frame()->peek_request = request_;
    auto input = h_.promise().input_interface();
    if (input) input->set_peek_request(request_);
  }

  auto await_resume() {
    auto input = h_.promise().input_interface();
    return input->peek(request_);
  }

 private:
  std::coroutine_handle<P> h_;
  std::size_t request_;
};

template <typename P>
peek_awaiter<P>::~peek_awaiter() {
  static_assert(Promise<P>);
}

/** Holds the result of a processor or processor_subtask. */
template <typename T>
using result_holder = std::variant<std::monostate, T, std::exception_ptr>;

template <typename R>
struct coroutine_return_mixin {
  result_holder<R> result;

  bool output_ready() const { return result.index() != 0; }

  R get_value_or_throw() {
    return visit(detail::overloaded{[](std::monostate&&) -> R {
                                      throw std::logic_error(
                                          "Attempted to read prematurely.");
                                    },
                                    [this](R&& r) -> R {
                                      auto v = std::move(r);
                                      result = std::monostate{};
                                      return v;
                                    },
                                    [this](std::exception_ptr&& ptr) -> R {
                                      auto p = std::move(ptr);
                                      result = std::monostate{};
                                      std::rethrow_exception(p);
                                    }},
                 std::move(result));
  }

  void return_value(R&& r)
    requires(!std::is_scalar_v<R>)
  {
    result = std::move(r);
  }
  void return_value(R r)
    requires(std::is_scalar_v<R>)
  {
    result = r;
  }
  void unhandled_exception() { result = std::current_exception(); }
};

template <>
struct coroutine_return_mixin<void> {
  struct ready {};
  result_holder<ready> result;

  bool output_ready() const { return result.index() != 0; }

  void get_value_or_throw() {
    return visit(
        overloaded{[](std::monostate&&) {
                     throw std::logic_error("Attempated to ready prematurely.");
                   },
                   [this](ready) { result = std::monostate{}; },
                   [this](std::exception_ptr&& ptr) {
                     auto p = std::move(ptr);
                     result = std::monostate{};
                     std::rethrow_exception(p);
                   }},
        std::move(result));
  }

  void return_void() { result = ready{}; }
  void unhandled_exception() { result = std::current_exception(); }
};

}  // namespace detail

template <typename In, typename R>
struct processor_subtask;

/**
 * A coroutine state object used to process streams.
 *
 * As a processor client, the idea is to provide one piece of input
 * data, read all output, and repeat. The stream can be reset if
 * necessary (e.g. because a lexing error requires that a
 * partially-parsed expression be abandoned). When the input stream is
 * complete, call `finish` and read any remaining output. Any of
 * `process`, `reset`, or `finish` may advance the stream, so after
 * calling one of those functions, the `processor` object must be
 * checked for additional output.
 *
 * Example usage:
 *  p = <get processor from coroutine factory>;
 *  while (event = pollEvent()) {
 *    if (event.type == CTRL_C) {
 *      p.reset();
 *      while (p) doSomethingWith(p());
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
 * You may also co_await on an instance of `peek` to preview a future
 * input. The return value for `peek{i}` is related to the ith future
 * call to `co_await next_input{}` (1-indexed). It is a value of a
 * type that can be evaluated in a boolean context (if true, a value
 * is available; if false, eof will be thrown at or before the ith
 * call to `co_await next_input{}`), or dereferenced with the `*`
 * operator to obtain the requested value. Awaiting on `peek` may also
 * throw `reset`. In this case, any output will be cleared, but any
 * input previewed through peeking without being consumed by awaiting
 * on `next_input` will still be returned by future awaits on
 * `next_input`.
 *
 * You may also co_await on a `processor_subtask` with a compatible
 * input type; see `processor_subtask`'s class documentation. If
 * `finish` has been called previously and intercepted by a subtask,
 * `co_await`ing on a subtask or `next_input` will result in `eof`
 * being thrown.
 *
 * Values must be produced using `co_yield`; `co_return` cannot be
 * used to produce the final value (but `co_return;` may be used to
 * finish the coroutine).
 *
 * `co_await` may only be applied to `next_input`, `peek` or
 * `processor_subtask`s. Awaiting on other types is not supported (and
 * will not compile).
 *
 * Example usage:
 *  processor<char, std::string> partition_into_words() {
 *      std::string word;
 *      while (true) {
 *          try {
 *              auto p = co_await peek{};
 *              while (p && !std::isalpha(*p)) co_await next_input {};
 *          } catch (reset) {
 *              continue;
 *          }
 *          char c;
 *          try {
 *              c = co_await next_input {};
 *          } catch (reset) {
 *              word.clear();
 *              continue;
 *          } catch (eof) {
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
  explicit operator bool() const { return handle_.promise().output_ready(); }

  /**
   * Returns the next product of processing.
   *
   * Throws if the coroutine has thrown an unhandled exception.
   */
  Out operator()() {
    auto value = handle_.promise().get_value_or_throw();
    resume();
    return value;
  }

  /** Provides data for processing. */
  void process(typename detail::input_traits<In>::input_type in) {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    if (handle_.promise().input->provide_input(in)) resume();
  }

  /** Provides data for processing. */
  void process(In&& in)
    requires(!std::is_scalar_v<In>)
  {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    if (handle_.promise().input->provide_input(std::move(in))) resume();
  }

  /** Discard any unprocessed data and start fresh. */
  void reset() {
    handle_.promise().reset();
    resume();
  }

  /** Signal that the input is complete. */
  void finish() {
    handle_.promise().input->finish();
    resume();
  }

  struct promise_type {
    using input_type = In;

    /** The input interface at the root of a processor call stack. */
    class root_input_interface : public detail::InputInterface<In> {
     public:
      using input_traits = detail::input_traits<In>;

      In get_input() override {
        if (reset_) {
          reset_ = false;
          struct reset r {};
          throw r;
        }

        if (eof_ && buf_.empty()) {
          throw eof{};
        }

        if (buf_.empty()) {
          throw std::logic_error("Attempted to resume without input");
        }

        auto in = std::move(buf_.front());
        buf_.pop_front();
        return in;
      }

      typename input_traits::peek_type peek(std::size_t i) override {
        if (i == 0) throw std::invalid_argument("i must be nonzero");

        if (reset_) {
          reset_ = false;
          struct reset r {};
          throw r;
        }

        if (i > buf_.size()) {
          if (!eof_)
            throw std::logic_error("Attempted to resume before peeking fully.");
          return input_traits::from_pointer(nullptr);
        }
        return input_traits::from_pointer(&buf_[i - 1]);
      }

      bool input_ready(std::size_t i) const override {
        return eof_ || reset_ || (i ? buf_.size() >= i : !buf_.empty());
      }

      bool input_complete() const override { return eof_ && buf_.empty(); }

      void set_peek_request(std::size_t peek_request) override {
        peek_request_ = peek_request;
      }

      void reset() {
        if (reset_ || eof_) throw std::logic_error("Spurious reset");
        reset_ = true;
      }

      void finish() {
        if (reset_ || eof_) throw std::logic_error("Spurious eof");
        eof_ = true;
      }

      template <typename T>
      bool provide_input(T&& in) {
        std::size_t target_size = peek_request_ + (peek_request_ == 0);
        if (buf_.size() >= target_size) {
          throw std::logic_error(
              "Must read output before providing more input.");
        }
        buf_.push_back(std::forward<T>(in));
        return buf_.size() == target_size;
      }

     private:
      bool reset_ = false;
      bool eof_ = false;
      std::size_t peek_request_ = 0;
      std::deque<In> buf_;
    };

    detail::result_holder<Out> value;
    std::shared_ptr<root_input_interface> input =
        std::make_shared<root_input_interface>();

    bool output_ready() const { return value.index() != 0; }

    Out get_value_or_throw() {
      return visit(
          detail::overloaded{
              [](std::monostate&&) -> Out {
                throw std::logic_error("Attempted to read when not ready.");
              },
              [this](Out&& out) -> Out {
                Out v = std::move(out);
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

    detail::processor_stack_frame* get_stack_frame() { return &frame_; }

    std::shared_ptr<detail::InputInterface<In>> input_interface() {
      return input;
    }

    void reset() {
      input->reset();
      value = std::monostate{};
    }

    std::suspend_always yield_value(const Out& v) {
      value = v;
      return {};
    }

    std::suspend_always yield_value(Out&& v) {
      value = std::move(v);
      return {};
    }

    void return_void() {}

    void unhandled_exception() { value = std::current_exception(); }

    processor get_return_object() { return processor{this}; }

    std::suspend_always initial_suspend() { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }

    template <typename I, typename SubR>
    [[nodiscard]] detail::subtask_awaiter<
        typename processor_subtask<I, SubR>::promise_type>
    await_transform(processor_subtask<I, SubR> task)
      requires(std::is_convertible_v<In, I>)
    {
      // Don't enter subtasks if input is complete.
      if (input->input_complete()) throw eof{};
      return detail::subtask_awaiter<
          typename processor_subtask<I, SubR>::promise_type>{task.handle_};
    }

    [[nodiscard]] detail::input_awaiter<promise_type> await_transform(
        next_input) {
      return detail::input_awaiter<promise_type>{
          handle_type::from_promise(*this)};
    }

    [[nodiscard]] detail::peek_awaiter<promise_type> await_transform(peek p) {
      return detail::peek_awaiter<promise_type>{
          handle_type::from_promise(*this), p.i};
    }

   private:
    detail::processor_stack_frame frame_{handle_type::from_promise(*this)};
  };

  processor(const processor&) = delete;
  processor(processor&& o) : handle_(std::exchange(o.handle_, nullptr)) {}

  ~processor() {
    if (handle_) handle_.destroy();
  }

 private:
  friend struct promise_type;

  static_assert(detail::Promise<promise_type>);

  explicit processor(promise_type* p)
      : handle_(handle_type::from_promise(*p)) {}

  void resume() { handle_.promise().get_stack_frame()->resume(); }

  handle_type handle_;
};

/**
 * A coroutine state object used for "helper" coroutines for `processor`s.
 *
 * A `processor_subtask` may be `co_await`ed upon either within a
 * `processor` coroutine, or within another `processor_subtask`
 * coroutine. The result of the `co_await` expression will be the
 * value of type `R` that was `co_return`ed by the subtask (or an
 * `eof` exception if a previously executed subtask intercepted an
 * `eof`, or an exception thrown by the subtask, including potentially
 * `eof` or `reset`).
 *
 * As in `processor`s, implementors of subtask coroutines may await on
 * `next_input`, `peek`, or other `processor_subtask` objects, with
 * the same semantics. A subtask coroutine must `co_return` a single
 * value or throw an exception.
 *
 * A subtask coroutine may safely intercept an `eof` and still
 * `co_return` a value. However, if `co_await` causes `reset` to be
 * thrown, it must be propagated to the caller.
 */
template <typename In, typename R>
struct [[nodiscard]] processor_subtask {
  struct promise_type;
  using handle_type = std::coroutine_handle<promise_type>;

  struct promise_type : public detail::coroutine_return_mixin<R> {
    using input_type = In;

    std::shared_ptr<detail::InputInterface<In>> input_interface() {
      if (input_) return input_;
      if (input_interface_callback_) input_ = input_interface_callback_();
      return input_;
    }

    void set_input_interface_callback(detail::InputInterfaceCallback<In>&& c) {
      input_interface_callback_ = std::move(c);
    }

    detail::processor_stack_frame* get_stack_frame() { return &frame_; }

    processor_subtask get_return_object() noexcept {
      return processor_subtask{this};
    }

    std::suspend_never initial_suspend() const noexcept { return {}; }

    std::suspend_always final_suspend() const noexcept { return {}; }

    template <typename I, typename SubR>
    [[nodiscard]] detail::subtask_awaiter<
        typename processor_subtask<I, SubR>::promise_type>
    await_transform(processor_subtask<I, SubR> task)
      requires(std::is_convertible_v<In, I>)
    {
      if (input_ && input_->input_complete()) throw eof{};
      return detail::subtask_awaiter<
          typename processor_subtask<I, SubR>::promise_type>{task.handle_};
    }

    [[nodiscard]] detail::input_awaiter<promise_type> await_transform(
        next_input) {
      return detail::input_awaiter<promise_type>{
          handle_type::from_promise(*this)};
    }

    [[nodiscard]] detail::peek_awaiter<promise_type> await_transform(peek p) {
      return detail::peek_awaiter<promise_type>{
          handle_type::from_promise(*this), p.i};
    }

   private:
    template <typename I, typename O>
    friend struct processor;

    detail::processor_stack_frame frame_{handle_type::from_promise(*this)};
    std::shared_ptr<detail::InputInterface<In>> input_;
    detail::InputInterfaceCallback<In> input_interface_callback_;
  };

  processor_subtask(const processor_subtask&) = delete;
  processor_subtask(processor_subtask&& o)
      : handle_(std::exchange(o.handle_, nullptr)) {}

  ~processor_subtask() {
    if (handle_) handle_.destroy();
  }

 private:
  friend struct promise_type;
  template <typename I, typename O>
  friend struct processor;
  template <typename I, typename O>
  friend struct processor_subtask;

  static_assert(detail::Promise<promise_type>);
  static_assert(detail::InnerPromise<promise_type>);

  explicit processor_subtask(promise_type* p)
      : handle_(handle_type::from_promise(*p)) {}

  handle_type handle_;
};

template <typename In, typename Out>
processor<In, Out> repeatedly(processor_subtask<In, Out> (*t)()) {
  while (true) {
    try {
      co_yield co_await t();
    } catch (reset) {
    } catch (eof) {
      co_return;
    }
  }
}

template <typename T>
using Expected = std::variant<T, std::exception_ptr>;

template <typename T>
T&& get_value_or_throw(Expected<T>&& e) {
  return visit(detail::overloaded{[](T&& t) -> T&& { return std::move(t); },
                                  [](std::exception_ptr&& p) -> T&& {
                                    std::rethrow_exception(p);
                                  }},
               std::move(e));
}

namespace detail {

/** Compose two pipelines. */
template <typename In, typename M1, typename M2, typename Out>
processor<In, Out> compose(processor<In, M1> in, processor<M2, Out> out) {
  bool done = false;
  while (!done) {
    try {
      in.process(co_await next_input{});
    } catch (reset) {
      in.reset();
      out.reset();
    } catch (eof) {
      in.finish();
      done = true;
    }
    while (out) co_yield out();
    while (in) {
      out.process(in());
      while (out) co_yield out();
    }
  }
  out.finish();
  while (out) co_yield out();
}

/** Compose two pipelines that may produce handled errors. */
template <typename In, typename M1, typename M2, typename Out>
processor<In, Expected<Out>> compose(processor<In, Expected<M1>> in,
                                     processor<M2, Expected<Out>> out) {
  bool done = false;
  while (!done) {
    try {
      in.process(co_await next_input{});
    } catch (reset) {
      in.reset();
      out.reset();
    } catch (eof) {
      in.finish();
      done = true;
    }
    while (out) co_yield out();
    while (in) {
      auto val = in();
      if (val.index() == 0) {
        out.process(get<0>(std::move(val)));
        while (out) co_yield out();
      } else {
        assert(val.index() == 1);
        co_yield get<1>(std::move(val));
        out.reset();
        while (out) co_yield out();
      }
    }
  }
  out.finish();
  while (out) co_yield out();
}

}  // namespace detail

/**
 * Compose two pipelines.
 *
 * Returns a processor with the following properties:
 *  - Expects `process` to be called with values of the same type `in` takes.
 *  - Produces values of the same type that `out` processes.
 *  - When reset, both `in` and `out` will be reset.
 *  - When finished, `in` will be finished, and the remainder of its output
 *    passed to `out`, which will then be finished.
 *
 * If `in` produces `Expected<M1>`, `out` takes something assignable
 * from `M1`, and `out` produces `Expected<T>` for some `T`, then an error
 * produced by `in` will cause `out` to be reset and the error
 * produced by `in` to be yielded as output.
 */
template <typename In, typename M1, typename M2, typename Out>
processor<In, Out> operator|(processor<In, M1>&& in, processor<M2, Out>&& out) {
  return detail::compose(std::move(in), std::move(out));
}

}  // namespace emil::processor
