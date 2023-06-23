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

#include "emil/processor.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <functional>
#include <string>
#include <vector>

namespace emil::processor::testing {
namespace {

using ::testing::ElementsAre;

/** Produces a stream of words (sequences of alphabetical characters). */
processor<char, std::string> partition_into_words() {
  std::string word;
  while (true) {
    char c;
    try {
      c = co_await next_input{};
    } catch (reset&) {
      word.clear();
      continue;
    } catch (eof&) {
      break;
    }
    if (std::isalpha(c)) {
      word.push_back(c);
    } else {
      if (!word.empty()) {
        co_yield std::move(word);
        word.clear();
      }
    }
  }
  if (!word.empty()) co_yield std::move(word);
}

TEST(ProcessorTest, BasicOperation) {
  const char input[] = "The quick brown fox jumped over the lazy dog.";
  auto p = partition_into_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("The", "quick", "brown", "fox", "jumped",
                                 "over", "the", "lazy", "dog"));
}

TEST(ProcessorTest, ThrowsWhenReadingAndNotReady) {
  auto p = partition_into_words();
  ASSERT_FALSE(p);
  EXPECT_THROW(p(), std::logic_error);
}

TEST(ProcessorTest, ThrowsOnDoubleWrite) {
  auto p = partition_into_words();
  ASSERT_FALSE(p);
  p.process('a');
  ASSERT_FALSE(p);
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p.process('f'), std::logic_error);
}

TEST(ProcessorTest, ResetClearsOutput) {
  auto p = partition_into_words();
  p.process('a');
  p.process(' ');
  ASSERT_TRUE(p);
  p.reset();
  ASSERT_FALSE(p);
}

struct sentence_fragment_exception {};

struct bad_char_exception {};

struct delayed_bad_char_exception {};

/**
 * Produces a stream of words from sentences.
 *
 * A word is a sequence of alphabetical characters. A sentence is any
 * sequence of characters ending in '.'.
 *
 * Throws `sentence_fragment_exception` if the input doesn't end in '.'.
 *
 * Throws `bad_char_exception` if a nonprintable character is passed.
 *
 * Throws `delayed_bad_char_exception` if any word that would be yielded
 * contains a capital 'Z'.
 */
processor<char, std::string> partition_sentences_into_words() {
  std::string buf;
  while (true) {
    try {
      char c = co_await next_input{};
      if (c < 32 || c > 126) throw bad_char_exception{};
      if (c == '.') {
        auto p = partition_into_words();
        for (char bc : buf) {
          p.process(bc);
          while (p) {
            auto word = p();
            if (word.contains('Z')) throw delayed_bad_char_exception{};
            co_yield std::move(word);
          }
        }
        p.finish();
        while (p) {
          auto word = p();
          if (word.contains('Z')) throw delayed_bad_char_exception{};
          co_yield std::move(word);
        }
        buf.clear();
      } else {
        buf.push_back(c);
      }
    } catch (reset&) {
      buf.clear();
    } catch (eof&) {
      if (!buf.empty()) throw sentence_fragment_exception{};
      break;
    }
  }
}

TEST(ProcessorTest, BasicNestedOperation) {
  const char input[] = "The quick brown fox jumped over the lazy dog.";
  auto p = partition_sentences_into_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("The", "quick", "brown", "fox", "jumped",
                                 "over", "the", "lazy", "dog"));
}

TEST(ProcessorTest, Reset) {
  const char input1[] = "Here are some words you won't see";
  const char input2[] = "The quick brown fox jumped over the lazy dog.";
  auto p = partition_sentences_into_words();
  std::vector<std::string> words;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("The", "quick", "brown", "fox", "jumped",
                                 "over", "the", "lazy", "dog"));
}

TEST(ProcessorTest, ExceptionThrownOnInput) {
  auto p = partition_sentences_into_words();
  p.process('\x01');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), bad_char_exception);
}

TEST(ProcessorTest, ExceptionThrownWhileYielding) {
  const char input[] = "Ze quick brown fox jumped over the lazy dog.";
  auto p = partition_sentences_into_words();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) {
      ASSERT_THROW(p(), delayed_bad_char_exception);
      return;
    }
  }
}

TEST(ProcessorTest, ExceptionThrownAfterFinish) {
  const char input[] = "The quick brown fox jumped over the lazy dog";
  auto p = partition_sentences_into_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), sentence_fragment_exception);
}

processor<std::string, std::string> alphabetize_words() {
  while (true) {
    try {
      auto word = co_await next_input{};
      std::ranges::sort(word);
      co_yield std::move(word);
    } catch (reset&) {
    } catch (eof&) {
      break;
    }
  }
}

TEST(ProcessorComposeTest, BasicOperation) {
  const char input[] = "The quick brown fox jumped over the lazy dog";
  auto p = partition_into_words() | alphabetize_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("Teh", "cikqu", "bnorw", "fox", "dejmpu",
                                 "eorv", "eht", "alyz", "dgo"));
}

TEST(ProcessorComposeTest, BasicNestedOperation) {
  const char input[] = "The quick brown fox jumped over the lazy dog.";
  auto p = partition_sentences_into_words() | alphabetize_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("Teh", "cikqu", "bnorw", "fox", "dejmpu",
                                 "eorv", "eht", "alyz", "dgo"));
}

TEST(ProcessorComposeTest, ResetInput) {
  const char input1[] = "Here are some words you won't see";
  const char input2[] = "The quick brown fox jumped over the lazy dog.";
  auto p = partition_sentences_into_words() | alphabetize_words();
  std::vector<std::string> words;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("Teh", "cikqu", "bnorw", "fox", "dejmpu",
                                 "eorv", "eht", "alyz", "dgo"));
}

/**
 * When it sees the word "STOP", returns the words since the last STOP
 * in alphabetical order.
 *
 * Throws `sentence_fragment_exception` if the input doesn't end in "STOP".
 *
 * Throws `bad_char_exception` if a word with a 'Y' is received.
 *
 * Throws `delayed_bad_char_exception` if any word that would be yielded
 * contains a capital 'Z'.
 */
processor<std::string, std::string> alphabetize_telegram_sentence() {
  std::vector<std::string> words;
  while (true) {
    try {
      auto word = co_await next_input{};
      if (word.contains('Y')) throw bad_char_exception{};
      if (word == "STOP") {
        std::ranges::sort(words);
        for (auto& w : words) {
          if (w.contains('Z')) throw delayed_bad_char_exception{};
          co_yield std::move(w);
        }
        words.clear();
      } else {
        words.push_back(std::move(word));
      }
    } catch (reset&) {
      words.clear();
    } catch (eof&) {
      if (!words.empty()) throw sentence_fragment_exception{};
      break;
    }
  }
}

TEST(ProcessorComposeTest, ResetOutput) {
  const char input1[] = "Here are some words you won't see";
  const char input2[] = "The quick brown fox jumped over the lazy dog STOP";
  auto p = partition_into_words() | alphabetize_telegram_sentence();
  std::vector<std::string> words;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  while (p) words.push_back(p());

  EXPECT_THAT(words, ElementsAre("The", "brown", "dog", "fox", "jumped", "lazy",
                                 "over", "quick", "the"));
}

TEST(ProcessorComposeTest, ExceptionThrownOnInput) {
  auto p = partition_sentences_into_words() | alphabetize_words();
  p.process('\x01');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), bad_char_exception);
}

TEST(ProcessorComposeTest, ExceptionThrownOnInputToOutput) {
  auto p = partition_into_words() | alphabetize_telegram_sentence();
  p.process('Y');
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), bad_char_exception);
}

TEST(ProcessorComposeTest, ExceptionThrownWhileYieldingInput) {
  const char input[] = "Ze quick brown fox jumped over the lazy dog STOP";
  auto p = partition_sentences_into_words() | alphabetize_telegram_sentence();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) {
      ASSERT_THROW(p(), delayed_bad_char_exception);
      return;
    }
  }
}

TEST(ProcessorComposeTest, ExceptionThrownWhileYieldingOutput) {
  const char input[] = "Ze quick brown fox jumped over the lazy dog STOP";
  auto p = partition_into_words() | alphabetize_telegram_sentence();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) {
      ASSERT_THROW(p(), delayed_bad_char_exception);
      return;
    }
  }
}

TEST(ProcessorComposeTest, ExceptionThrownAfterFinishInput) {
  const char input[] = "The quick brown fox jumped over the lazy dog";
  auto p = partition_sentences_into_words() | alphabetize_words();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), sentence_fragment_exception);
}

TEST(ProcessorComposeTest, ExceptionThrownAfterFinishOutput) {
  const char input[] = "The quick brown fox jumped over the lazy dog";
  auto p = partition_into_words() | alphabetize_telegram_sentence();
  std::vector<std::string> words;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) words.push_back(p());
  }
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), sentence_fragment_exception);
}

}  // namespace
}  // namespace emil::processor::testing
