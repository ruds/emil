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
#include <exception>
#include <functional>
#include <stdexcept>
#include <utility>
#include <variant>

namespace emil::processor {

/** Marker class used by coroutines returning `processor` or
 * `processor_subtask`. */
struct next_input {};
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

template <typename T>
using InputCallback = std::function<T()>;

/** Used to track the execution stack of `processor_subtask`s. */
struct processor_stack_frame {
  std::coroutine_handle<> handle;
  processor_stack_frame* outer = nullptr;
  processor_stack_frame* inner = nullptr;
  /** Indicates that eof has been received on a descendant task. */
  bool finished_on_inner = false;

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

template <typename P>
concept Promise = requires(P p) {
  typename P::input_type;
  p.get_value_or_throw();
  { p.get_input_or_throw() } -> std::convertible_to<typename P::input_type>;
  { p.get_stack_frame() } -> std::same_as<processor_stack_frame*>;
  { p.output_ready() } -> std::convertible_to<bool>;
};

template <typename P>
concept RootPromise = requires(P p) {
  { p.input_ready() } -> std::convertible_to<bool>;
};

template <typename P>
concept InnerPromise = requires(P p) {
  typename P::input_type;
  p.set_input_callback(std::declval<InputCallback<typename P::input_type>>());
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
    inner_frame->outer = outer_frame;
    // When we resume later, we'll need to read the input from the
    // root of the call tree. We don't have direct access to it, so we
    // need to call up the chain after each intervening level has been
    // linked in this way.
    handle_.promise().set_input_callback([caller]() {
      assert(caller);
      return caller.promise().get_input_or_throw();
    });
    if constexpr (RootPromise<P2>) {
      // If there's already input available, we can resume immediately.
      if (caller.promise().input_ready()) {
        outer_frame->resume();
      }
    } else {
      static_assert(InnerPromise<P2>);
    }
  }

  // Returns the `co_return`ed value and unlinks the inner frame.
  auto await_resume() {
    assert(handle_);
    assert(handle_.promise().output_ready());
    auto* frame = handle_.promise().get_stack_frame();
    if (frame->outer) frame->outer->inner = nullptr;
    return handle_.promise().get_value_or_throw();
  }

 private:
  std::coroutine_handle<P> handle_;
};

template <typename P>
subtask_awaiter<P>::~subtask_awaiter() {
  static_assert(Promise<P>);
}

/** Manages the execution of `co_await next_input{}`. */
template <typename P>
struct input_awaiter {
  explicit input_awaiter(std::coroutine_handle<P> h) : h_(h) {}
  ~input_awaiter();

  bool await_ready() {
    assert(h_);
    // If a subtask already get EOF, we know our answer already.
    if (h_.promise().get_stack_frame()->finished_on_inner) return true;
    if constexpr (RootPromise<P>) {
      // We already have input, no need to suspend.
      return h_.promise().input_ready();
    } else {
      static_assert(InnerPromise<P>);
      // If we're an inner task, we always have to suspend when we're asking for
      // input.
      return false;
    }
  }

  void await_suspend(std::coroutine_handle<P> h) { h_ = h; }

  auto await_resume() {
    auto* frame = h_.promise().get_stack_frame();
    if (frame->finished_on_inner) {
      frame->finished_on_inner = false;
      throw eof{};
    }
    try {
      return h_.promise().get_input_or_throw();
    } catch (eof) {
      frame = frame->outer;
      while (frame) {
        frame->finished_on_inner = true;
        frame = frame->outer;
      }
      throw;
    }
  }

 private:
  std::coroutine_handle<P> h_;
};

template <typename P>
input_awaiter<P>::~input_awaiter() {
  static_assert(Promise<P>);
}

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
 * `co_await` may only be applied to `next_input` or `processor_subtask`s.
 * Awaiting on other types is not supported (and will not compile).
 *
 * Example usage:
 *  processor<char, std::string> partition_into_words() {
 *      std::string word;
 *      while (true) {
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
  void process(const In& in) {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    handle_.promise().provide_input(in);
    resume();
  }

  /** Provides data for processing. */
  void process(In&& in) {
    if (*this) {
      throw std::logic_error(
          "Must read all output before providing more input.");
    }
    handle_.promise().provide_input(std::move(in));
    resume();
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

  struct promise_type {
    std::variant<std::monostate, Out, std::exception_ptr> value;
    using input_type = In;
    std::variant<std::monostate, In, struct reset, eof> input;

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

    bool input_ready() const { return input.index() != 0; }

    In get_input_or_throw() {
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

    detail::processor_stack_frame* get_stack_frame() { return &frame_; }

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
      struct reset r {};
      input = r;
      value = std::monostate{};
    }

    void finish() { input = eof{}; }

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
      if (frame_.finished_on_inner) throw eof{};
      return detail::subtask_awaiter<
          typename processor_subtask<I, SubR>::promise_type>{task.handle_};
    }

    [[nodiscard]] detail::input_awaiter<promise_type> await_transform(
        next_input) {
      return detail::input_awaiter<promise_type>{
          handle_type::from_promise(*this)};
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
  static_assert(detail::RootPromise<promise_type>);

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
 * Implementors of subtask coroutines may `co_await next_input{}` as
 * in `processor` coroutines to get the next input (or an `eof` or
 * `reset` being thrown). They may also `co_await` on other
 * `processor_subtask`s with compatible input types. A subtask
 * coroutine must `co_return` a single value or throw an exception.
 *
 * A subtask coroutine may safely intercept an `eof` and still
 * `co_return` a value. However, if `co_await` causes `reset` to be
 * thrown, it must be propagated to the caller.
 */
template <typename In, typename R>
struct [[nodiscard]] processor_subtask {
  struct promise_type;
  using handle_type = std::coroutine_handle<promise_type>;

  struct promise_type {
    using input_type = In;

    std::variant<std::monostate, R, std::exception_ptr> result;

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

    In get_input_or_throw() {
      assert(input_callback_);
      return input_callback_();
    }

    void set_input_callback(detail::InputCallback<In>&& c) {
      input_callback_ = std::move(c);
    }

    detail::processor_stack_frame* get_stack_frame() { return &frame_; }

    processor_subtask get_return_object() noexcept {
      return processor_subtask{this};
    }

    void return_value(R&& r) { result = std::move(r); }

    void unhandled_exception() { result = std::current_exception(); }

    std::suspend_never initial_suspend() const noexcept { return {}; }

    std::suspend_always final_suspend() const noexcept { return {}; }

    template <typename I, typename SubR>
    [[nodiscard]] detail::subtask_awaiter<
        typename processor_subtask<I, SubR>::promise_type>
    await_transform(processor_subtask<I, SubR> task)
      requires(std::is_convertible_v<In, I>)
    {
      if (frame_.finished_on_inner) throw eof{};
      return detail::subtask_awaiter<
          typename processor_subtask<I, SubR>::promise_type>{task.handle_};
    }

    [[nodiscard]] detail::input_awaiter<promise_type> await_transform(
        next_input) {
      return detail::input_awaiter<promise_type>{
          handle_type::from_promise(*this)};
    }

   private:
    template <typename I, typename O>
    friend struct processor;

    detail::processor_stack_frame frame_{handle_type::from_promise(*this)};
    detail::InputCallback<In> input_callback_;
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
      continue;
    } catch (eof) {
      in.finish();
      done = true;
    }
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
      continue;
    } catch (eof) {
      in.finish();
      done = true;
    }
    while (in) {
      auto val = in();
      if (val.index() == 0) {
        out.process(get<0>(std::move(val)));
        while (out) co_yield out();
      } else {
        assert(val.index() == 1);
        out.reset();
        co_yield get<1>(std::move(val));
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
