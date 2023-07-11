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

/**
 * @file processor.h
 *
 * @brief Provides a coroutine-based stream processing framework.
 *
 * The library provides three primary types for stream processor
 * authors, one of which is important for stream processor users.
 *
 * Users
 * =====
 *
 * This primary type is `processor<In, Out>`, a coroutine return
 * object that processes a stream of `In` to produce a stream of
 * `Out`. To use a `processor<In, Out>`, provide it with an
 * element of input with `process()`, then read output as long
 * as the `processor` evaluates to `true` with `operator()()`.
 * When the input stream is complete, call `finish()` and read
 * any final output.
 *
 * A brief example:
 *
 *     processor<char, std::string> words();
 *
 *     std::vector<std::string> w;
 *     auto p = words();
 *     for (char c : input) {
 *         p.process(c);
 *         while (p) w.push_back(p());
 *     }
 *     p.finish();
 *     while (p) w.push_back(p());
 *
 * `processor<In, Out>` also provides `reset()`, which indicates to
 * the stream processor that any partially processed input should be
 * discarded. The exact semantics of this reset should be documented
 * by the author of the stream processor. Just as with `process()`
 * and `finish()`, after calling `reset()` any output should be
 * drained from the `processor`. For example, a `processor` converting
 * tokens to abstract syntax trees may need to be reset if a lexing
 * error requires that the current token sequence be discarded.
 *
 * `processor`s can be composed using the `|` operator, where the
 * output type of the left-hand side is convertible to the input type
 * of the right-hand side. Composing two `processor`s that produce
 * `Expected` values has special semantics; see the documentation for
 * `operator|()`.
 *
 * A more complicated example:
 *
 *     processor<std::string, char> chars();
 *     processor<char, std::string> words();
 *
 *     auto p = chars() | words();
 *     while (event = pollConsole()) {
 *         if (event.type == CTRL_C) {
 *             p.reset();
 *             while (p) doSomethingWith(p());
 *         } else if (event.type == CTRL_D) {
 *             p.finish();
 *             while (p) doSomethingWith(p());
 *             break;
 *         } else {
 *             p.process(event.data());
 *             while (p) doSomethingWith(p());
 *         }
 *     }
 *
 * Library Authors
 * ===============
 *
 * `processor`
 * -----------
 *
 * To write a `processor` coroutine, there are only 5 concepts that can
 * be `co_await`ed.
 *
 * 1. To consume the next element of the input stream,
 *    `co_await next_input{}`. There are 3 possible outcomes:
 *
 *    - The next element of the input stream is returned due to the
 *      caller's call to `process()`.
 *    - `reset` is thrown due to the caller's call to `reset()`.
 *    - `eof` is thrown due to the caller's call to `finish()`.
 *
 *    Neither `reset` nor `eof` may be propagated beyond the coroutine.
 *
 * 2. To look ahead the ith buffered future element of the input stream,
 *    `co_await peek{i}`. The default value of `i` if omitted is 1, which
 *    indicates that the next element should be buffered. This returns
 *    something that acts like a pointer to the input type (but e.g. for
 *    a scalar type is a `std::optional`). To get the exact type, use
 *    `detail::input_type<T>::peek_type`, but generally it is best to
 *    use `auto`, and interact only through boolean evaluation and
 *    dereferencing using `operator*()`. The value will evaluate to
 *    false if the input stream will end before the ith element can be
 *    read, and true otherwise.
 *
 * 3. To call a `subtask`, you co_await on it, which will evaluate to
 *    the value `co_return`ed by the `subtask` (or throw `eof`,
 *    `reset`, or anything the `subtask` coroutine happens to throw).
 *    In particular, it will throw `eof` if `finish()` has been called
 *    and no further input is buffered. See below for more about subtasks.
 *
 * 4. To determine whether a `subprocess` has more output available,
 *    `co_await` on the value returned by its `done()` function.
 *
 * 5. To read the next output element from a `subprocess`, `co_await`
 *    on the `subprocess`. See below for more about `subprocesses.`
 *
 * Attempting to `co_await` on other types will not compile.
 *
 * To produce output elements, `co_yield` one at a time. `co_return`
 * may only be called without a value.
 *
 * Example usage:
 *
 *     processor<char, std::string> words() {
 *         std::string word;
 *         while (true) {
 *             auto p = co_await peek{};
 *             while (p && !std::isalpha(*p)) {
 *                 co_await next_input{};
 *                 p = co_await peek{};
 *             }
 *         } catch (reset) {
 *             continue;
 *         }
 *         char c;
 *         try {
 *             c = co_await next_input {};
 *         } catch (reset) {
 *             word.clear();
 *             continue;
 *         } catch (eof) {
 *             break;
 *         }
 *         if (std::isalpha(c)) {
 *             word.push_back(c);
 *         } else if (!word.empty()) {
 *             co_yield std::move(word);
 *             word.clear();
 *         }
 *         if (!word.empty()) co_yield(std::move(word));
 *     }
 *
 * `subprocess`
 * ------------
 *
 * A `subprocess` is a `processor` that shares a lookahead buffer with
 * its caller. This allows peeking ahead in either the caller or the
 * subprocess coroutine without the danger of discarding input.
 *
 * A `subprocess<In, Out>` is obtained by calling `as_subprocess()` on
 * an rvalue of type `processor<In, Out>`. This must be done before any
 * other interaction with the `processor`, which is left in a null state
 * and is only suitable for destruction or being assigned to.
 *
 * The `subprocess` will produce data as long as `co_await done()` is
 * true; its output is obtained by `co_await`ing on the `subprocess`
 * itself.
 *
 * Example usage:
 *
 *     auto subp = get_process().as_subprocess();
 *     while (!co_await subp.done()) {
 *         auto next = co_await subp;
 *         // do something with next, e.g. co_yield.
 *     }
 *
 * Unlike top-level processors, a subprocess coroutine may throw
 * `reset` or `eof`, or alternatively it may swallow either. The rules
 * for implementing a subprocess coroutine are otherwise identical to
 * those for implementing a processor coroutine.
 *
 * `subtask`
 * ---------
 *
 * A `subtask` is a coroutine that shares a lookahead buffer with its
 * caller and may process 0 or more elements of the input stream,
 * while producing a single value.
 *
 * A subtask coroutine may `co_await` on any of the first 3 types
 * allowed by a `processor`; it may not `co_await` on
 * `subprocess.done()` or `subprocess` objects.
 *
 * Unlike `processor`s, a `subtask` may allow `eof` to propagate to
 * its caller, though it may also safely handle `eof` and still
 * `co_return` a value. However, it *must* allow `reset` to propagate
 * to its caller.
 */

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

#include "emil/misc.h"

namespace emil::processor {

/** Marker class used by coroutines returning `processor` or
 * `subtask` to request the next input item. */
struct next_input {};
/** Marker class used by coroutines returning `processor` or
 * `subtask` to request a preview of the `i`th future input item. */
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

/** Used to track the execution stack of `subtask`s. */
struct processor_stack_frame {
  std::coroutine_handle<> handle;
  processor_stack_frame* inner = nullptr;
  processor_stack_frame* outer = nullptr;
  /** If nonzero, a request to peek ahead the given number of inputs. */
  std::size_t peek_request = 0;

  explicit processor_stack_frame(std::coroutine_handle<> h) : handle(h) {}

  /** Resumes execution of the innermost stack frame. */
  void resume() {
    assert(handle);
    assert(!handle.done());
    innermost_handle().resume();
  }

  /** The handle of the innermost stack frame. */
  std::coroutine_handle<> innermost_handle() {
    auto* frame = this;
    while (frame->inner) frame = frame->inner;
    assert(frame->handle);
    assert(!frame->handle.done());
    return frame->handle;
  }
};

/** Type traits for the input type for a processor/subtask. */
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

/** Produce an InputInterface<In>. */
template <typename In>
std::shared_ptr<InputInterface<In>> input_interface(
    std::shared_ptr<InputInterface<In>>&& in) {
  return std::move(in);
}

/** Delegates to another InputInterface, performing implicit type conversion. */
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

/** Produce an InputInterface<In>. */
template <typename RequestedIn, typename AvailableIn>
std::shared_ptr<InputInterface<RequestedIn>> input_interface(
    std::shared_ptr<InputInterface<AvailableIn>>&& in)
  requires(!std::is_same_v<RequestedIn, AvailableIn>)
{
  return std::make_shared<DelegatingInputInterface<RequestedIn, AvailableIn>>(
      std::move(in));
}

/** Processors have an input interface with some extended operations. */
template <typename In>
struct ProcessorInputInterfaceBase : public InputInterface<In> {
  virtual void reset() = 0;
  virtual void finish() = 0;
};

template <typename In>
struct ProcessorInputInterface : public ProcessorInputInterfaceBase<In> {
  virtual bool provide_input(In&& in) = 0;
  virtual bool provide_input(const In& in) = 0;
};

template <scalar In>
struct ProcessorInputInterface<In> : public ProcessorInputInterfaceBase<In> {
  virtual bool provide_input(In in) = 0;
};

/** Produce a ProcessorInputInterface<In>. */
template <typename In>
std::shared_ptr<ProcessorInputInterface<In>> processor_input_interface(
    std::shared_ptr<ProcessorInputInterface<In>> in) {
  return std::move(in);
}

/** Produce an InputInterface<In>. */
template <typename In>
std::shared_ptr<InputInterface<In>> input_interface(
    std::shared_ptr<ProcessorInputInterface<In>>&& in) {
  return std::move(in);
}

/** Delegates to another ProcessorInputInterface, performing implicit type
 * conversion. */
template <typename RequestedIn, typename AvailableIn>
struct DelegatingProcessorInputInterfaceBase
    : public ProcessorInputInterface<RequestedIn> {
  explicit DelegatingProcessorInputInterfaceBase(
      std::shared_ptr<ProcessorInputInterface<AvailableIn>>&& delegate)
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

  void reset() override { delegate_->reset(); }
  void finish() override { delegate_->finish(); }

 protected:
  std::shared_ptr<ProcessorInputInterface<AvailableIn>> delegate_;
};

template <typename RequestedIn, typename AvailableIn>
struct DelegatingProcessorInputInterface
    : public DelegatingProcessorInputInterfaceBase<RequestedIn, AvailableIn> {
  using DelegatingProcessorInputInterfaceBase<
      RequestedIn, AvailableIn>::DelegatingProcessorInputInterfaceBase;

  bool provide_input(RequestedIn&& in) override {
    return this->delegate_->provide_input(std::move(in));
  }

  bool provide_input(const RequestedIn& in) override {
    return this->delegate_->provide_input(in);
  }
};

template <scalar RequestedIn, typename AvailableIn>
struct DelegatingProcessorInputInterface<RequestedIn, AvailableIn>
    : public DelegatingProcessorInputInterfaceBase<RequestedIn, AvailableIn> {
  using DelegatingProcessorInputInterfaceBase<
      RequestedIn, AvailableIn>::DelegatingProcessorInputInterfaceBase;

  bool provide_input(const RequestedIn& in) override {
    return this->delegate_->provide_input(in);
  }
};

/** Produce a ProcessorInputInterface<In>. */
template <typename RequestedIn, typename AvailableIn>
std::shared_ptr<ProcessorInputInterface<RequestedIn>> processor_input_interface(
    std::shared_ptr<ProcessorInputInterface<AvailableIn>> in)
  requires(!std::is_same_v<RequestedIn, AvailableIn>)
{
  return std::make_shared<
      DelegatingProcessorInputInterface<RequestedIn, AvailableIn>>(
      std::move(in));
}

/** Produce an InputInterface<In>. */
template <typename RequestedIn, typename AvailableIn>
std::shared_ptr<InputInterface<RequestedIn>> input_interface(
    std::shared_ptr<ProcessorInputInterface<AvailableIn>>&& in)
  requires(!std::is_same_v<RequestedIn, AvailableIn>)
{
  return std::make_shared<DelegatingInputInterface<RequestedIn, AvailableIn>>(
      std::move(in));
}

/** The shared concept for promises associated with processors, subtasks, etc.
 */
template <typename P>
concept Promise = requires(P p) {
  typename P::input_type;
  p.get_value_or_throw();
  { p.get_stack_frame() } -> std::same_as<processor_stack_frame*>;
  { p.output_ready() } -> std::convertible_to<bool>;
  {
    p.input_interface()
  } -> std::convertible_to<
      std::shared_ptr<InputInterface<typename P::input_type>>>;
};

/** The concept extension for promises associated with subtasks. */
template <typename P>
concept SubtaskPromise = requires(P p) {
  typename P::input_type;
  p.set_input_interface_callback(
      std::declval<InputInterfaceCallback<typename P::input_type>>());
};

/** Suspends the current coroutine to resume the given coroutine. */
struct coro_awaiter {
  bool await_ready() const noexcept { return false; }
  void await_resume() const noexcept {}

  std::coroutine_handle<> await_suspend(std::coroutine_handle<>) noexcept {
    return h;
  }

  std::coroutine_handle<> h;
};

/** Manages the execution of `co_await subtask`. */
template <typename P>
struct subtask_awaiter {
  explicit subtask_awaiter(std::coroutine_handle<P> h) : handle_(h) {}
  ~subtask_awaiter();

  // We're considering suspending the task for one of two reasons.
  // Either the task has completed, or it has stopped to ask for
  // input. If it's completed, we don't actually need to suspend it
  // and we're ready to resume immediately.
  bool await_ready() const noexcept {
    assert(handle_);
    return handle_.done();
  }

  template <Promise P2>
  std::coroutine_handle<> await_suspend(std::coroutine_handle<P2> caller) {
    assert(handle_);
    // Link the frame of the calling coroutine to the frame of the
    // coroutine being suspended. That will allow us to resume the inner
    // coroutine later.
    auto* outer_frame = caller.promise().get_stack_frame();
    auto* inner_frame = handle_.promise().get_stack_frame();
    outer_frame->inner = inner_frame;
    inner_frame->outer = outer_frame;
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
      // If there's already input available, we can resume the innermost frame
      // immediately.
      if (input->input_ready(inner_frame->peek_request)) {
        return inner_frame->innermost_handle();
      } else {
        input->set_peek_request(inner_frame->peek_request);
      }
    }
    return std::noop_coroutine();
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
  static_assert(Promise<P> && SubtaskPromise<P>);
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

/** Holds the result of a processor or subtask. */
template <typename T>
using result_holder = std::variant<std::monostate, T, std::exception_ptr>;

/** Provides output-related methods for the subtask promise. */
template <typename R>
struct coroutine_return_mixin {
  result_holder<R> result;

  bool output_ready() const { return result.index() != 0; }

  R get_value_or_throw() {
    return visit(
        overloaded{[](std::monostate&&) -> R {
                     throw std::logic_error("Attempted to read prematurely.");
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

/** Specializes for subtasks that return void. */
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

template <typename In, typename Out>
struct processor_promise;

/** Monitors the state of a processor. */
enum ProcessorState {
  /** Initial state; nothing has committed it to either path. */
  UNCOMMITTED,
  /** This is a root process; it cannot be made into a subprocess. */
  ROOT,
  /** This is a subprocess that does not yet have access to its parent input. */
  SUBPROCESS_UNLINKED,
  /** This is the final form of a subprocess with access to its full power. */
  SUBPROCESS_LINKED,
};

inline bool is_subprocess(ProcessorState p) {
  return p == SUBPROCESS_LINKED || p == SUBPROCESS_UNLINKED;
}

}  // namespace detail

template <typename In, typename Out>
struct processor;

/**
 * Manages co_await subprocess.done().
 *
 * The major issue this solves is that when a subprocess yields, we can't
 * continue execution until its caller has read that output. So we wait
 * until the caller has read the output and checked for done-ness, and then
 * resume the subprocess until its next suspend point.
 */
template <typename In, typename Out>
struct subprocess_done {
  using handle_type = std::coroutine_handle<detail::processor_promise<In, Out>>;

  bool await_ready() const noexcept {
    return !handle_ || handle_.done() || !handle_.promise().yielded_last ||
           handle_.promise().output_ready();
  }

  template <detail::Promise P>
  std::coroutine_handle<> await_suspend(std::coroutine_handle<P> caller) {
    auto* outer_frame = caller.promise().get_stack_frame();
    auto* inner_frame = handle_.promise().get_stack_frame();
    assert(!outer_frame->inner);
    outer_frame->inner = inner_frame;
    inner_frame->outer = outer_frame;
    return handle_;
  }

  bool await_resume() const noexcept { return !handle_ || handle_.done(); }

  explicit subprocess_done(handle_type h) : handle_(h) {}

 private:
  handle_type handle_;
};

/**
 * A subprocess is a process that shares its lookahead buffer with its parent.
 *
 * Example usage:
 *
 *     auto subp = get_process().as_subprocess();
 *     while (!co_await subp.done()) {
 *         auto next = co_await subp;
 *         // do something with next, e.g. co_yield.
 *     }
 *
 * Unlike top-level processes, a subprocess may throw `reset` or `eof`, or
 * alternatively it may swallow either. As in top-level processes, attempting
 * to `co_await` a subtask or subprocess when `co_await next_input{}`has
 * previously thrown `eof` will throw `eof`.
 */
template <typename In, typename Out>
struct subprocess {
  using handle_type = std::coroutine_handle<detail::processor_promise<In, Out>>;

  /** When `co_await done()` is true, there's no more output. */
  subprocess_done<In, Out> done() { return subprocess_done{handle_}; }

  subprocess(const subprocess&) = delete;
  subprocess& operator=(const subprocess&) = delete;

  subprocess(subprocess&& o) noexcept
      : handle_(std::exchange(o.handle_, nullptr)) {}

  subprocess& operator=(subprocess&& o) noexcept {
    handle_ = std::exchange(o.handle_, nullptr);
    return *this;
  }

  bool await_ready() {
    if (!handle_ || handle_.done())
      throw std::logic_error("Can't co_await a finished subprocess");
    auto& p = handle_.promise();
    return p.state == detail::SUBPROCESS_LINKED && p.output_ready();
  }

  template <detail::Promise P>
  std::coroutine_handle<> await_suspend(std::coroutine_handle<P> caller) {
    assert(handle_);

    auto* outer_frame = caller.promise().get_stack_frame();
    auto* inner_frame = handle_.promise().get_stack_frame();
    outer_frame->peek_request = inner_frame->peek_request;
    assert(!outer_frame->inner);
    outer_frame->inner = inner_frame;
    inner_frame->outer = outer_frame;

    auto input = caller.promise().input_interface();
    assert(input);
    auto& p = handle_.promise();
    if (p.state == detail::SUBPROCESS_UNLINKED) {
      p.state = detail::SUBPROCESS_LINKED;
      p.input = processor_input_interface<In>(input);

      if (p.output_ready()) {
        return caller;
      }
    }

    if (input->input_ready(inner_frame->peek_request)) {
      return inner_frame->innermost_handle();
    }
    input->set_peek_request(inner_frame->peek_request);
    return std::noop_coroutine();
  }

  Out await_resume() {
    assert(handle_);
    assert(handle_.promise().output_ready());
    return handle_.promise().get_value_or_throw();
  }

 private:
  friend struct processor<In, Out>;

  explicit subprocess(handle_type handle) : handle_(handle) {
    assert(handle_);
    assert(!handle_.done());
    assert(handle_.promise().state == detail::UNCOMMITTED);
    handle_.promise().state = detail::SUBPROCESS_UNLINKED;
    handle_.promise().input = nullptr;
    handle_.resume();
  }

  void resume() { handle_.promise().get_stack_frame()->resume(); }

  handle_type handle_;
};

/**
 * A coroutine state object used to process streams.
 */
template <typename In, typename Out>
struct [[nodiscard]] processor {
  using promise_type = detail::processor_promise<In, Out>;
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
    if (handle_.promise().provide_input(in)) resume();
  }

  /** Provides data for processing. */
  void process(In&& in)
    requires(!std::is_scalar_v<In>)
  {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    if (handle_.promise().provide_input(std::move(in))) resume();
  }

  /** Discard any unprocessed data and start fresh. */
  void reset() {
    handle_.promise().reset();
    resume();
  }

  /** Signal that the input is complete. */
  void finish() {
    handle_.promise().finish();
    resume();
  }

  /**
   * Converts to a `subprocess`.
   *
   * Must be called on an rvalue before any other interaction; leaves
   * this object in a null state.
   */
  subprocess<In, Out> as_subprocess() && {
    if (!handle_ || handle_.promise().state != detail::UNCOMMITTED) {
      throw std::logic_error("Must convert to subprocess before interacting");
    }
    return subprocess<In, Out>{std::exchange(handle_, nullptr)};
  }

  processor(const processor&) = delete;
  processor& operator=(const processor&) = delete;

  processor(processor&& o) noexcept
      : handle_(std::exchange(o.handle_, nullptr)) {}

  processor& operator=(processor&& o) noexcept {
    handle_ = std::exchange(o.handle_, nullptr);
    return *this;
  }

  processor() : handle_(nullptr) {}

  ~processor() {
    if (handle_) handle_.destroy();
  }

 private:
  friend struct detail::processor_promise<In, Out>;

  static_assert(detail::Promise<promise_type>);

  explicit processor(promise_type* p)
      : handle_(handle_type::from_promise(*p)) {}

  void resume() { handle_.promise().get_stack_frame()->resume(); }

  handle_type handle_;
};

/**
 * A coroutine state object used for "helper" coroutines for `processor`s.
 */
template <typename In, typename R>
struct [[nodiscard]] subtask {
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

    subtask get_return_object() noexcept { return subtask{this}; }

    std::suspend_never initial_suspend() const noexcept { return {}; }

    detail::coro_awaiter final_suspend() const noexcept {
      if (frame_.outer) {
        frame_.outer->inner = nullptr;
        return {frame_.outer->handle};
      }
      return {std::noop_coroutine()};
    }

    template <typename I, typename SubR>
    [[nodiscard]] detail::subtask_awaiter<
        typename subtask<I, SubR>::promise_type>
    await_transform(subtask<I, SubR> task)
      requires(std::is_convertible_v<In, I>)
    {
      if (input_ && input_->input_complete()) throw eof{};
      return detail::subtask_awaiter<typename subtask<I, SubR>::promise_type>{
          task.handle_};
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

  subtask(const subtask&) = delete;
  subtask(subtask&& o) : handle_(std::exchange(o.handle_, nullptr)) {}

  ~subtask() {
    if (handle_) handle_.destroy();
  }

 private:
  friend struct promise_type;
  template <typename, typename>
  friend struct detail::processor_promise;
  template <typename, typename>
  friend struct processor;
  template <typename, typename>
  friend struct subtask;

  static_assert(detail::Promise<promise_type>);
  static_assert(detail::SubtaskPromise<promise_type>);

  explicit subtask(promise_type* p) : handle_(handle_type::from_promise(*p)) {}

  handle_type handle_;
};

/** Repeatedly call `t`, streaming its co_returned values. */
template <typename In, typename Out>
processor<In, Out> repeatedly(subtask<In, Out> (*t)()) {
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
  return visit(overloaded{[](T&& t) -> T&& { return std::move(t); },
                          [](std::exception_ptr&& p) -> T&& {
                            std::rethrow_exception(p);
                          }},
               std::move(e));
}

namespace detail {

/** The input interface at the root of a processor call stack. */
template <typename In>
class processor_promise_input_interface_base
    : public detail::ProcessorInputInterface<In> {
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

  void reset() override {
    if (reset_ || eof_) throw std::logic_error("Spurious reset");
    reset_ = true;
  }

  void finish() override {
    if (reset_ || eof_) throw std::logic_error("Spurious eof");
    eof_ = true;
  }

  template <typename T>
  bool actually_provide_input(T&& in) {
    std::size_t target_size = peek_request_ + (peek_request_ == 0);
    if (buf_.size() >= target_size) {
      throw std::logic_error("Must read output before providing more input.");
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

template <typename In>
struct processor_promise_input_interface
    : public processor_promise_input_interface_base<In> {
  bool provide_input(In&& in) override {
    return this->actually_provide_input(std::move(in));
  }

  bool provide_input(const In& in) override {
    return this->actually_provide_input(in);
  }
};

template <scalar In>
struct processor_promise_input_interface<In>
    : public processor_promise_input_interface_base<In> {
  bool provide_input(In in) override {
    return this->actually_provide_input(in);
  }
};

/** The promise type for `processor` (and `subprocess`). */
template <typename In, typename Out>
struct processor_promise {
  using input_type = In;
  using handle_type = std::coroutine_handle<processor_promise>;

  detail::result_holder<Out> value;
  std::shared_ptr<detail::ProcessorInputInterface<In>> input =
      std::make_shared<processor_promise_input_interface<In>>();
  ProcessorState state = UNCOMMITTED;
  /** True when the most recent suspension of this coroutine was due to
   * `co_yield`. */
  bool yielded_last = false;

  bool output_ready() const { return value.index() != 0; }

  Out get_value_or_throw() {
    return visit(
        overloaded{
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
              if (is_subprocess(state)) {
                std::rethrow_exception(p);
              } else {
                try {
                  std::rethrow_exception(p);
                } catch (struct reset) {
                  throw std::logic_error("Coroutine doesn't handle reset.");
                } catch (eof) {
                  throw std::logic_error("Coroutine doesn't handle finish.");
                }
              }
            }},
        std::move(value));
  }

  detail::processor_stack_frame* get_stack_frame() { return &frame_; }

  std::shared_ptr<detail::ProcessorInputInterface<In>> input_interface() {
    if (state == UNCOMMITTED) state = ROOT;
    return input;
  }

  void reset() {
    if (is_subprocess(state))
      throw std::logic_error("Cannot call reset on subprocess");
    state = ROOT;
    input->reset();
    value = std::monostate{};
  }

  void finish() {
    if (is_subprocess(state))
      throw std::logic_error("Cannot call finish on subprocess");
    state = ROOT;
    input->finish();
  }

  template <typename T>
  bool provide_input(T&& in) {
    if (is_subprocess(state))
      throw std::logic_error("Cannot call process on subprocess");
    state = ROOT;
    return input->provide_input(std::forward<T>(in));
  }

  detail::coro_awaiter yield_value(Out v)
    requires(std::is_scalar_v<Out>)
  {
    yielded_last = true;
    value = v;
    if (frame_.outer) {
      assert(is_subprocess(state));
      frame_.outer->inner = nullptr;
      return {frame_.outer->handle};
    }
    return {std::noop_coroutine()};
  }

  detail::coro_awaiter yield_value(const Out& v)
    requires(!std::is_scalar_v<Out>)
  {
    yielded_last = true;
    value = v;
    if (frame_.outer) {
      assert(is_subprocess(state));
      frame_.outer->inner = nullptr;
      return {frame_.outer->handle};
    }
    return {std::noop_coroutine()};
  }

  detail::coro_awaiter yield_value(Out&& v)
    requires(!std::is_scalar_v<Out>)
  {
    yielded_last = true;
    value = std::move(v);
    if (frame_.outer) {
      assert(is_subprocess(state));
      frame_.outer->inner = nullptr;
      return {frame_.outer->handle};
    }
    return {std::noop_coroutine()};
  }

  void return_void() { yielded_last = false; }

  void unhandled_exception() {
    yielded_last = false;
    value = std::current_exception();
  }

  processor<In, Out> get_return_object() { return processor{this}; }

  std::suspend_always initial_suspend() { return {}; }

  coro_awaiter final_suspend() noexcept {
    if (frame_.outer) {
      assert(is_subprocess(state));
      frame_.outer->inner = nullptr;
      return {frame_.outer->handle};
    }
    return {std::noop_coroutine()};
  }

  template <typename I, typename SubR>
  [[nodiscard]] detail::subtask_awaiter<typename subtask<I, SubR>::promise_type>
  await_transform(subtask<I, SubR> task)
    requires(std::is_convertible_v<In, I>)
  {
    yielded_last = false;
    // Don't enter subtasks if input is complete.
    if (input && input->input_complete()) throw eof{};
    return detail::subtask_awaiter<typename subtask<I, SubR>::promise_type>{
        task.handle_};
  }

  [[nodiscard]] detail::input_awaiter<processor_promise> await_transform(
      next_input) {
    yielded_last = false;
    return detail::input_awaiter<processor_promise>{
        handle_type::from_promise(*this)};
  }

  [[nodiscard]] detail::peek_awaiter<processor_promise> await_transform(
      peek p) {
    yielded_last = false;
    return detail::peek_awaiter<processor_promise>{
        handle_type::from_promise(*this), p.i};
  }

  template <typename I, typename O>
  [[nodiscard]] subprocess<I, O>& await_transform(subprocess<I, O>& s) {
    yielded_last = false;
    // Don't enter subprocesses if input is complete.
    if (input && input->input_complete()) throw eof{};
    return s;
  }

  template <typename I, typename O>
  [[nodiscard]] subprocess_done<I, O> await_transform(subprocess_done<I, O> s) {
    yielded_last = false;
    return s;
  }

 private:
  detail::processor_stack_frame frame_{handle_type::from_promise(*this)};
};

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
                                     processor<M2, Expected<Out>> out)
  requires(!std::is_convertible_v<Expected<M1>, M2>)
{
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
