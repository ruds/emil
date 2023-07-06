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

#include <fmt/core.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <exception>
#include <functional>
#include <ostream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace emil::processor::testing {
namespace {

using ::testing::ElementsAre;
using ::testing::Eq;

struct handled_exception_in_partition {};
struct unhandled_exception_in_partition_at_finish {};
struct unhandled_exception_in_partition_on_input {};
struct unhandled_exception_in_partition_on_yield {};

struct handled_exception_in_sort {};
struct unhandled_exception_in_sort_at_finish {};
struct unhandled_exception_in_sort_on_input {};
struct unhandled_exception_in_sort_on_yield {};

/** Produces a stream of words (sequences of alphabetical characters). */
processor<char, std::string> partition_into_words() {
  std::string word;
  while (true) {
    char c;
    try {
      c = co_await next_input{};
    } catch (reset) {
      word.clear();
      continue;
    } catch (eof) {
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
    } catch (reset) {
      buf.clear();
    } catch (eof) {
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

processor_subtask<char, std::string> extract_word() {
  std::string word;
  char c;
  try {
    for (c = co_await next_input{}; std::isalpha(c);
         c = co_await next_input{}) {
      if (c == 'Z') throw unhandled_exception_in_partition_on_input{};
      word.push_back(c);
    }
  } catch (eof) {
  }
  if (word.contains('Y')) throw unhandled_exception_in_partition_on_yield{};
  co_return word;
}

processor<char, std::vector<std::string>>
alphabetize_sentences_using_subtask() {
  std::vector<std::string> sentence;
  while (true) {
    try {
      std::string word = co_await extract_word();
      if (word == "BADINPUT") throw unhandled_exception_in_sort_on_input{};
      if (word == "STOP") {
        std::ranges::sort(sentence);
        if (std::ranges::binary_search(sentence, "BADOUTPUT"))
          throw unhandled_exception_in_sort_on_yield{};
        co_yield std::move(sentence);
        sentence.clear();
      } else {
        sentence.push_back(std::move(word));
      }
    } catch (reset) {
      sentence.clear();
    } catch (eof) {
      if (!sentence.empty()) throw unhandled_exception_in_sort_at_finish{};
      break;
    }
  }
}

TEST(ProcessorSingleSubtaskTest, BasicOperation) {
  const char input[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = alphabetize_sentences_using_subtask();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(p());
  }
  p.finish();
  while (p) sorted_sentences.push_back(p());

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorSingleSubtaskTest, Reset) {
  const char input1[] = "Wont see these words you know ";
  const char input2[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = alphabetize_sentences_using_subtask();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(p());
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(p());
  }
  p.finish();
  while (p) sorted_sentences.push_back(p());

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorSingleSubtaskTest, ErrorInSubtask) {
  const char input[] = "Wont see Zis ";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) {
    p.process(*c);
  }
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_on_input);
}

TEST(ProcessorSingleSubtaskTest, ErrorInSubtaskOnReturn) {
  const char input[] = "Wont see Yis";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) {
    p.process(*c);
  }
  ASSERT_FALSE(p);
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_on_yield);
}

TEST(ProcessorSingleSubtaskTest, ErrorInSubtaskAfterFinish) {
  const char input[] = "Wont see Yis";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) {
    p.process(*c);
  }
  ASSERT_FALSE(p);
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_on_yield);
}

TEST(ProcessorSingleSubtaskTest, ErrorInProcessorOnInput) {
  const char input[] = "BADINPUT";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) p.process(*c);
  ASSERT_FALSE(p);
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_on_input);
}

TEST(ProcessorSingleSubtaskTest, ErrorInProcessorOnYield) {
  const char input[] = "BADOUTPUT foo bar STOP";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) p.process(*c);
  ASSERT_FALSE(p);
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_on_yield);
}

TEST(ProcessorSingleSubtaskTest, ErrorInProcessorOnFinish) {
  const char input[] = "foo bar baz";
  auto p = alphabetize_sentences_using_subtask();
  for (const char* c = input; *c && !p; ++c) p.process(*c);
  ASSERT_FALSE(p);
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_at_finish);
}

struct scored_sentence {
  int key_score;
  int sentence_score;
  std::string trailer;

  friend bool operator==(const scored_sentence&, const scored_sentence&);
};

[[maybe_unused]] bool operator==(const scored_sentence&,
                                 const scored_sentence&) = default;

[[maybe_unused]] void PrintTo(const scored_sentence& s, std::ostream* out) {
  *out << fmt::format("{{key_score: {}, sentence_score: {}, trailer: {}}}",
                      s.key_score, s.sentence_score, s.trailer);
}

scored_sentence score(int key_score, int sentence_score, std::string trailer) {
  return {key_score, sentence_score, std::move(trailer)};
}

struct score_word_error_on_input {};
struct score_word_recoverable_error {};
struct score_word_error_on_return {};
struct score_sentence_error_on_input {};
struct score_sentence_error_on_return {};
struct score_sentences_error_on_input {};
struct score_sentences_error_on_yield {};

/**
 * Read a word from the input and score it.
 *
 * Reads and discards non-alphabetic characters until reading one or
 * more alphabetic characters followed by a non-alphabetic character
 * or the end of the file. The score is the sum of the ascii values of
 * the alphabetic characters.
 *
 * If a 'Z' is read, throws `score_word_error_on_input`.
 *
 * If an 'X' is read, throws `score_word_recoverable_error`.
 *
 * If BADWORD (or any other word with a score of 515) is read, throws
 * `score_word_error_on_return`.
 */
processor_subtask<int, int> score_word() {
  std::string word;
  int c;
  while (!std::isalpha(c = co_await next_input{})) {
  }
  int sum = 0;
  try {
    do {
      if (c == 'Z') throw score_word_error_on_input{};
      if (c == 'X') throw score_word_recoverable_error{};
      sum += c;
    } while (std::isalpha(c = co_await next_input{}));
  } catch (eof) {
  }
  if (sum == 515) throw score_word_error_on_return{};  // BADWORD
  co_return sum;
}

/**
 * Read a sentence from the input and score it.
 *
 * Reads and scores words using `score_word`. A sentence is ended by
 * STOP (or any other word with a score of 326). The sentence's score
 * is the sum of the scores of all the words excluding the stop-word.
 *
 * If BADSWORD (or any other word with a score of 598) is read, throws
 * `score_sentence_error_on_input`.
 *
 * If a full sentence is read with a score less than 300, throws
 * `score_sentence_error_on_return`.
 *
 * Also throws any exceptions thrown by `score_word`.
 */
processor_subtask<char, int> score_sentence() {
  int sum = 0;
  while (true) {
    int w = co_await score_word();
    if (w == 598) throw score_sentence_error_on_input{};  // BADSWORD
    if (w == 326) {                                       // STOP
      if (sum < 300) throw score_sentence_error_on_return{};
      co_return sum;
    }
    sum += w;
  }
}

/**
 * Read a stream of "scored sentences" from the input.
 *
 * A scored sentence consists of a word (as defined by `score_word`),
 * called the key, a sentence (as defined by `score_sentence`), and
 * another word, called the trailer. For each sentence, a
 * `scored_sentence` including the key's score, the sentence's score,
 * and the actual trailer, is produced.
 *
 * If the key is BADKEY (or any other word with a score of 432),
 * throws `score_sentences_error_on_input`.
 *
 * If the trailer is BADTRAILER, throws `score_sentences_error_on_yield`.
 *
 * If `score_word` or `score_sentence` throws
 * `score_word_recoverable_error`, discards the current
 * `scored_sentence` and re-synchronizes with the stream by reading
 * until a stop-word is read along with the word following it,
 * discarding that input.
 *
 * Also throws any other exception thrown by `score_word` or
 * `score_sentence`.
 */
processor<char, scored_sentence> score_sentences() {
  bool done = false;
  bool needs_to_synchronize = false;
  while (!done) {
    scored_sentence result{};
    try {
      try {
        result.key_score = co_await score_word();
        if (result.key_score == 432)  // BADKEY
          throw score_sentences_error_on_input{};
        result.sentence_score = co_await score_sentence();
        char c;
        while (!std::isalpha(c = co_await next_input{})) {
        }
        do {
          result.trailer.push_back(c);
        } while (std::isalpha(c = co_await next_input{}));
      } catch (score_word_recoverable_error) {
        needs_to_synchronize = true;
      }
      if (needs_to_synchronize) {
        while ((co_await score_word()) != 326) {
        }  // STOP
        co_await score_word();
        needs_to_synchronize = false;
        continue;
      }
    } catch (reset) {
      continue;
    } catch (eof) {
      done = true;
    }
    if (result.trailer == "BADTRAILER") throw score_sentences_error_on_yield{};
    co_yield std::move(result);
  }
}

TEST(ProcessorNestedSubtaskTest, BasicOperation) {
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, ResetInKey) {
  const char lost_input[] = "key";
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = lost_input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.reset();
  ASSERT_FALSE(p);
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, ResetInSentence) {
  const char lost_input[] = "key sentence is here";
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = lost_input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.reset();
  ASSERT_FALSE(p);
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, ResetInTrailer) {
  const char lost_input[] = "key sentence is here STOP trail";
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = lost_input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.reset();
  ASSERT_FALSE(p);
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, FinishInKey) {
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum key";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores, ElementsAre(score(324, 626, "quux"),
                                  score(304, 622, "fum"), score(329, 0, "")));
}

TEST(ProcessorNestedSubtaskTest, FinishInSentence) {
  const char input[] =
      "foo bar baz STOP quux fee fie foe STOP fum key half value";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores, ElementsAre(score(324, 626, "quux"),
                                  score(304, 622, "fum"), score(329, 0, "")));
}

TEST(ProcessorNestedSubtaskTest, ErrorInKeyOnInput) {
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  p.process('Z');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_word_error_on_input);
}

TEST(ProcessorNestedSubtaskTest, ErrorInNestedWordOnInput) {
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  p.process('f');
  p.process(' ');
  p.process('Z');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_word_error_on_input);
}

TEST(ProcessorNestedSubtaskTest, ErrorInSentenceOnInput) {
  const char input[] = "key BADSWORD";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_sentence_error_on_input);
}

TEST(ProcessorNestedSubtaskTest, ErrorInTopLevelOnInput) {
  const char input[] = "BADKEY";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_sentences_error_on_input);
}

TEST(ProcessorNestedSubtaskTest, RecoverableErrorInKey) {
  const char lost_input[] = "Xe old STOP trailer ";
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = lost_input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, RecoverableErrorInNestedWordInSentence) {
  const char lost_input[] = "Bike BMX STOP trailer ";
  const char input[] = "foo bar baz STOP quux fee fie foe STOP fum";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = lost_input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) scores.push_back(p());
  }
  p.finish();
  while (p) scores.push_back(p());

  EXPECT_THAT(scores,
              ElementsAre(score(324, 626, "quux"), score(304, 622, "fum")));
}

TEST(ProcessorNestedSubtaskTest, ErrorInKeyOnReturn) {
  const char input[] = "BADWORD";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_word_error_on_return);
}

TEST(ProcessorNestedSubtaskTest, ErrorInNestedWordOnReturn) {
  const char input[] = "key BADWORD";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_word_error_on_return);
}

TEST(ProcessorNestedSubtaskTest, ErrorInSentenceOnReturn) {
  const char input[] = "key bad STOP";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_sentence_error_on_return);
}

TEST(ProcessorNestedSubtaskTest, ErrorInTopLevelOnYield) {
  const char input[] = "key nice sentence STOP BADTRAILER";
  std::vector<scored_sentence> scores;
  auto p = score_sentences();
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    ASSERT_FALSE(p);
  }
  p.process(' ');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), score_sentences_error_on_yield);
}

struct subtask_unexpected_eof {};
struct subtask_unexpected_input {};

/**
 * Processes one command.
 *
 * Reads one char to determine the command.
 *
 * If the command is:
 * - 'C': Reads an additional character to determine the
 *   count, then reads `count` characters and returns them
 *   as a string. If eof is reached before `count`
 *   characters have been read, throws subtask_unexpected_eof.
 * - 'P': Reads an additional character to determine the
 *   count, then peeks ahead `count` characters and returns
 *   the last as a one-character string.
 * - Anything else: throws subtask_unexpected_input.
 */
processor_subtask<char, std::string> peek_machine_subtask() {
  try {
    switch (co_await next_input{}) {
      case 'P': {
        std::size_t count = co_await next_input{};
        auto c = co_await peek{count};
        co_return c ? std::string(1, *c) : "∅";
      }

      case 'C': {
        std::size_t count = co_await next_input{};
        std::string out;
        while (count--) {
          out += co_await next_input{};
        }
        co_return out;
      }

      default:
        throw subtask_unexpected_input{};
    }
  } catch (eof) {
    throw subtask_unexpected_eof{};
  }
}

struct task_unexpected_eof {};
struct task_unexpected_input {};

/**
 * Processes one command.
 *
 * Reads one char to determine the command.
 *
 * If the command is:
 * - 'C': Reads an additional character to determine the
 *   count, then reads `count` characters and returns them
 *   as a string. If eof is reached before `count`
 *   characters have been read, throws task_unexpected_eof.
 * - 'P': Reads an additional character to determine the
 *   count, then peeks ahead `count` characters and returns
 *   the last as a one-character string.
 * - 'S': Calls peek_machine_subtask to process an additional
 *   command.
 * - Anything else: throws task_unexpected_input.
 */
processor_subtask<char, std::string> peek_machine_task() {
  try {
    auto command = co_await next_input{};
    switch (command) {
      case 'P': {
        std::size_t count = co_await next_input{};
        auto c = co_await peek{count};
        co_return c ? std::string(1, *c) : "∅";
      }

      case 'C': {
        std::size_t count = co_await next_input{};
        std::string out;
        while (count--) {
          out += co_await next_input{};
        }
        co_return out;
      }

      case 'S': {
        co_return co_await peek_machine_subtask();
      }

      default:
        throw task_unexpected_input{};
    }
  } catch (eof) {
    throw task_unexpected_eof{};
  }
}

struct processor_unexpected_eof {};
struct processor_unexpected_input {};

/**
 * Processes commands.
 *
 * As long as input lasts, reads one char to determine the command.
 *
 * If the command is:
 * - 'C': Reads an additional character to determine the
 *   count, then reads `count` characters and returns them
 *   as a string. If eof is reached before `count`
 *   characters have been read, throws processor_unexpected_eof.
 * - 'P': Reads an additional character to determine the
 *   count, then peeks ahead `count` characters and returns
 *   the last as a one-character string.
 * - 'T': Calls peek_machine_task to process an additional
 *   command.
 * - Anything else: throws processor_unexpected_input.
 *
 * If reset while processing a command, discards partial results
 * and starts over with reading a command character.
 */
processor<char, std::string> peek_machine_processor() {
  while (true) {
    char command;
    try {
      command = co_await next_input{};
    } catch (eof) {
      co_return;
    } catch (reset) {
      continue;
    }
    try {
      switch (command) {
        case 'P': {
          std::size_t count = co_await next_input{};
          auto c = co_await peek{count};
          co_yield c ? std::string(1, *c) : "∅";
          break;
        }

        case 'C': {
          std::size_t count = co_await next_input{};
          std::string out;
          while (count--) {
            out += co_await next_input{};
          }
          co_yield out;
          break;
        }

        case 'T': {
          co_yield co_await peek_machine_task();
          break;
        }

        default:
          throw task_unexpected_input{};
      }
    } catch (eof) {
      throw task_unexpected_eof{};
    } catch (reset) {
    }
  }
}

template <typename P>
void feed_string(std::string_view s, P& processor) {
  for (char c : s) {
    ASSERT_FALSE(processor);
    processor.process(c);
  }
}

TEST(ProcessorPeekTest, BasicOperation) {
  // input: C5helloP3C5worldP5P1
  auto p = peek_machine_processor();

  feed_string("C\5hello", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("hello"));
  ASSERT_FALSE(p);

  feed_string("P\3C\5w", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("w"));
  ASSERT_FALSE(p);

  feed_string("orld", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("world"));
  ASSERT_FALSE(p);

  feed_string("P\5P\1", p);
  ASSERT_FALSE(p);

  p.finish();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_FALSE(p);
}

TEST(ProcessorPeekTest, ResetRetainsBuffer) {
  auto p = peek_machine_processor();

  feed_string("P\6C\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));
}

TEST(ProcessorTaskPeekTest, BasicOperation) {
  // input: TC5helloTP3C5worldTP5P1
  auto p = peek_machine_processor();

  feed_string("TC\5hello", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("hello"));
  ASSERT_FALSE(p);

  feed_string("TP\3C\5w", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("w"));
  ASSERT_FALSE(p);

  feed_string("orld", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("world"));
  ASSERT_FALSE(p);

  feed_string("TP\5P\1", p);
  ASSERT_FALSE(p);

  p.finish();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_FALSE(p);
}

TEST(ProcessorTaskPeekTest, ResetRetainsBuffer) {
  auto p = peek_machine_processor();

  feed_string("TP\6C\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));

  feed_string("TP\7TC\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));
}

TEST(ProcessorNestedTaskPeekTest, BasicOperation) {
  // input: TC5helloTSP4TC5worldTSP5P1
  auto p = peek_machine_processor();

  feed_string("TC\5hello", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("hello"));
  ASSERT_FALSE(p);

  feed_string("TSP\4TC\5w", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("w"));
  ASSERT_FALSE(p);

  feed_string("orld", p);
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("world"));
  ASSERT_FALSE(p);

  feed_string("TSP\5P\1", p);
  ASSERT_FALSE(p);

  p.finish();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("∅"));
  ASSERT_FALSE(p);
}

TEST(ProcessorNestedTaskPeekTest, ResetRetainsBuffer) {
  auto p = peek_machine_processor();

  feed_string("TSP\6C\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));

  feed_string("TSP\7TC\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));

  feed_string("TSP\10TSC\3oop", p);
  ASSERT_FALSE(p);
  p.reset();
  ASSERT_TRUE(p);
  ASSERT_THAT(p(), Eq("oop"));
}

processor<std::string, std::string> alphabetize_words() {
  while (true) {
    try {
      auto word = co_await next_input{};
      std::ranges::sort(word);
      co_yield std::move(word);
    } catch (reset) {
    } catch (eof) {
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
    } catch (reset) {
      words.clear();
    } catch (eof) {
      if (!words.empty()) throw sentence_fragment_exception{};
      break;
    }
  }
}

TEST(ProcessorComposeTest, ResetOutput) {
  const char input1[] = "Here are some words you won't see ";
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

struct sentence_insufficient_lookahead {};

processor<std::string, std::vector<std::string>> peeking_sentence_processor() {
  std::deque<std::string> buf;
  auto first = co_await next_input{};
  std::size_t lookahead = std::stoul(first);
  for (std::size_t i = 0; i < lookahead; ++i) {
    auto p = co_await peek{i + 1};
    if (!p) throw sentence_insufficient_lookahead{};
    buf.push_back(*p);
  }

  bool needs_reset = false;
  while (!buf.empty()) {
    std::vector<std::string> sentence;

    try {
      while (!buf.empty() && (sentence.empty() || sentence.back() != "STOP")) {
        auto p = co_await peek{lookahead + 1};
        if (p) buf.push_back(*p);

        sentence.push_back(co_await next_input{});
        assert(sentence.back() == buf.front());
        buf.pop_front();
      }
      if (sentence.back() == "STOP") sentence.pop_back();
      if (needs_reset) {
        sentence.clear();
        needs_reset = false;
      } else {
        co_yield std::move(sentence);
        sentence.clear();
      }
    } catch (reset) {
      needs_reset = true;
      continue;
    }
  }
  try {
    co_await next_input{};
    assert(false);
  } catch (eof) {
    co_return;
  }
}

TEST(ProcessorPeekComposeTest, BasicOperation) {
  const char input[] = "P\5C\3hi5C\5worldC\4STOPP\11C\1uC\5there";
  auto p = peek_machine_processor() | peeking_sentence_processor();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(p());
  }
  p.finish();
  while (p) sentences.push_back(p());

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeTest, ResetInput) {
  const char wont_see[] = "C\0011C\4oopsP\10C\4STOP";
  const char input[] = "C\3hi5C\5worldC\4STOPP\11C\1uC\5there";
  auto p = peek_machine_processor() | peeking_sentence_processor();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(p());
  }
  p.reset();
  while (p) sentences.push_back(p());
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(p());
  }
  p.finish();
  while (p) sentences.push_back(p());

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeTest, ResetOutput) {
  const char wont_see[] = "C\0011C\4oops";
  const char input[] = "C\4STOPC\3hi5C\5worldC\4STOPP\11C\1uC\5there";
  auto p = peek_machine_processor() | peeking_sentence_processor();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(p());
  }
  p.reset();
  while (p) sentences.push_back(p());
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(p());
  }
  p.finish();
  while (p) sentences.push_back(p());

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

/**
 * Partitions a stream into words.
 *
 * Buffers three words before sending.
 *
 * If there are any buffered words when the input is complete, throws
 * unhandled_exception_in_partition_at_finish.
 *
 * If any character is not printable ASCII, throws
 * unhandled_exception_in_partition_on_input.
 *
 * If any word that would be yielded contains a capital 'Z', throws
 * unhandled_exception_in_partition_on_yield.
 *
 * If any character is '@', yields handled_exception_in_partition.
 */
processor<char, Expected<std::string>> partition_words_with_errors() {
  std::vector<std::string> word_buf;
  std::string char_buf;
  bool done = false;
  while (!done) {
    try {
      char c = co_await next_input{};
      if (c == '@') {
        char_buf.clear();
        word_buf.clear();
        co_yield std::make_exception_ptr(handled_exception_in_partition{});
        continue;
      } else if (c < 32 || c > 126) {
        throw unhandled_exception_in_partition_on_input{};
      } else if (std::isalpha(c)) {
        char_buf.push_back(c);
        continue;
      } else {
      }
    } catch (reset) {
      char_buf.clear();
      word_buf.clear();
    } catch (eof) {
      done = true;
    }
    if (!char_buf.empty()) {
      word_buf.push_back(std::move(char_buf));
      char_buf.clear();
      if (word_buf.size() == 3) {
        for (auto& w : word_buf) {
          if (w.contains('Z'))
            throw unhandled_exception_in_partition_on_yield{};
          co_yield std::move(w);
        }
        word_buf.clear();
      }
    }
  }
  if (!word_buf.empty()) throw unhandled_exception_in_partition_at_finish{};
}

/**
 * Sorts words in sentences.
 *
 * A sentence ends with (but does not include) the word STOP.
 *
 * If there are any buffered words when the input is complete, throws
 * unhandled_exception_in_sort_at_finish.
 *
 * If any word is "BADINPUT", throws unhandled_exception_in_sort_on_input.
 *
 * If any word that would be yielded is "BADOUTPUT", throws
 * unhandled_exception_in_sort_on_yield.
 *
 * If any word is "HANDLED", yields handled_exception_in_sort.
 */
processor<std::string, Expected<std::vector<std::string>>>
sort_sentences_with_errors() {
  std::vector<std::string> buf;
  while (true) {
    try {
      std::string word = co_await next_input{};
      if (word == "BADINPUT") {
        throw unhandled_exception_in_sort_on_input{};
      } else if (word == "HANDLED") {
        buf.clear();
        co_yield std::make_exception_ptr(handled_exception_in_sort{});
      } else if (word == "STOP") {
        std::ranges::sort(buf);
        if (std::ranges::binary_search(buf, "BADOUTPUT"))
          throw unhandled_exception_in_sort_on_yield{};
        co_yield std::move(buf);
        buf.clear();
      } else {
        buf.push_back(std::move(word));
      }
    } catch (reset) {
      buf.clear();
    } catch (eof) {
      if (!buf.empty()) throw unhandled_exception_in_sort_at_finish{};
      co_return;
    }
  }
}

TEST(ProcessorComposeWithErrorsTest, BasicOperation) {
  const char input[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sorted_sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorComposeWithErrorsTest, ResetPartition) {
  const char input1[] = "Wont see";
  const char input2[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sorted_sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorComposeWithErrorsTest, HandledErrorInPartition) {
  const char input1[] = "Wont see these words @";
  const char input2[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
  }
  ASSERT_TRUE(p);
  ASSERT_THROW(get_value_or_throw(p()), handled_exception_in_partition);
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sorted_sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorComposeWithErrorsTest, ResetSort) {
  const char input1[] = "Wont see these words you know ";
  const char input2[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.reset();
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sorted_sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorComposeWithErrorsTest, HandledErrorInSort) {
  const char input1[] = "Wont see these words because HANDLED ";
  const char input2[] =
      "The quick brown fox STOP jumped over the lazy dog STOP STOP";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  std::vector<std::vector<std::string>> sorted_sentences;
  for (const char* c = input1; *c; ++c) {
    p.process(*c);
  }
  ASSERT_TRUE(p);
  ASSERT_THROW(get_value_or_throw(p()), handled_exception_in_sort);
  for (const char* c = input2; *c; ++c) {
    p.process(*c);
    while (p) sorted_sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sorted_sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sorted_sentences,
              ElementsAre(ElementsAre("The", "brown", "fox", "quick"),
                          ElementsAre("dog", "jumped", "lazy", "over", "the"),
                          ElementsAre()));
}

TEST(ProcessorComposeWithErrorsTest, ExceptionOnPartitionInput) {
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  p.process('\x01');
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_on_input);
}

TEST(ProcessorComposeWithErrorsTest, ExceptionOnSortInput) {
  const char input[] = "word word BADINPUT ";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  for (const char* c = input; *c; ++c) p.process(*c);
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_on_input);
}

TEST(ProcessorComposeWithErrorsTest, ExceptionOnPartitionYield) {
  const char input[] = "word Zee word ";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  for (const char* c = input; *c; ++c) p.process(*c);
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_on_yield);
}

TEST(ProcessorComposeWithErrorsTest, ExceptionOnSortYield) {
  const char input[] = "word BADOUTPUT STOP ";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  for (const char* c = input; *c; ++c) p.process(*c);
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_on_yield);
}

TEST(ProcessorComposeWithErrorsTest, ExceptionAtPartitionFinish) {
  const char input[] = "word word ";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  for (const char* c = input; *c; ++c) p.process(*c);
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_partition_at_finish);
}

TEST(ProcessorComposeWithErrorsTest, ExceptionAtSortFinish) {
  const char input[] = "word word word ";
  auto p = partition_words_with_errors() | sort_sentences_with_errors();
  for (const char* c = input; *c; ++c) p.process(*c);
  p.finish();
  ASSERT_TRUE(p);
  EXPECT_THROW(p(), unhandled_exception_in_sort_at_finish);
}

processor_subtask<char, void> advance_past_semicolon() {
  while ((co_await next_input{}) != ';') {
  }
}

processor<char, Expected<std::string>> peek_machine_processor_with_errors() {
  bool needs_reset = false;
  while (true) {
    if (needs_reset) {
      co_await advance_past_semicolon();
      needs_reset = false;
    }
    char command;
    try {
      command = co_await next_input{};
    } catch (eof) {
      co_return;
    } catch (reset) {
      continue;
    }
    try {
      switch (command) {
        case 'P': {
          std::size_t count = co_await next_input{};
          auto c = co_await peek{count};
          if ((co_await next_input{}) != ';') {
            co_yield std::make_exception_ptr(processor_unexpected_input{});
            needs_reset = true;
            break;
          }
          co_yield c ? std::string(1, *c) : "∅";
          break;
        }

        case 'C': {
          std::size_t count = co_await next_input{};
          std::string out;
          while (count--) {
            out += co_await next_input{};
          }
          if ((co_await next_input{}) != ';') {
            co_yield std::make_exception_ptr(processor_unexpected_input{});
            needs_reset = true;
            break;
          }
          co_yield out;
          break;
        }

        default:
          co_yield std::make_exception_ptr(processor_unexpected_input{});
          needs_reset = true;
      }
    } catch (eof) {
      throw task_unexpected_eof{};
    } catch (reset) {
      needs_reset = true;
    } catch (std::invalid_argument) {
      needs_reset = true;
    }
  }
}

struct sentence_unexpected_input {};

processor<std::string, Expected<std::vector<std::string>>>
peeking_sentence_processor_with_errors() {
  std::deque<std::string> buf;
  auto first = co_await next_input{};
  std::size_t lookahead = std::stoul(first);
  for (std::size_t i = 0; i < lookahead; ++i) {
    auto p = co_await peek{i + 1};
    if (!p) throw sentence_insufficient_lookahead{};
    buf.push_back(*p);
  }

  bool needs_reset = false;
  while (!buf.empty()) {
    std::vector<std::string> sentence;

    try {
      while (!buf.empty() && (sentence.empty() || sentence.back() != "STOP")) {
        auto p = co_await peek{lookahead + 1};
        if (p) buf.push_back(*p);

        sentence.push_back(co_await next_input{});
        assert(sentence.back() == buf.front());
        buf.pop_front();
        if (sentence.back() == "ERROR") {
          co_yield std::make_exception_ptr(sentence_unexpected_input{});
          needs_reset = true;
        }
      }
      if (sentence.back() == "STOP") sentence.pop_back();
      if (needs_reset) {
        sentence.clear();
        needs_reset = false;
      } else {
        co_yield std::move(sentence);
        sentence.clear();
      }
    } catch (reset) {
      needs_reset = true;
      continue;
    }
  }
  try {
    co_await next_input{};
    assert(false);
  } catch (eof) {
    co_return;
  }
}

TEST(ProcessorPeekComposeWithErrorsTest, BasicOperation) {
  const char input[] = "P\6;C\3hi5;C\5world;C\4STOP;P\13;C\1u;C\5there;";
  auto p = peek_machine_processor_with_errors() |
           peeking_sentence_processor_with_errors();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeWithErrorsTest, ResetPeekMachine) {
  const char wont_see[] = "C\0011;C\4oops;P\10;C\4STOP;";
  const char input[] = "C\3hi5;C\5world;C\4STOP;P\13;C\1u;C\5there;";
  auto p = peek_machine_processor_with_errors() |
           peeking_sentence_processor_with_errors();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.reset();
  while (p) sentences.push_back(get_value_or_throw(p()));
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeWithErrorsTest, ErrorInPeekMachine) {
  const char wont_see[] = "C\0011;C\4oops;";
  const char input[] =
      "garbage;C\4STOP;C\3hi5;C\5world;C\4STOP;P\13;C\1u;C\5there;";
  auto p = peek_machine_processor_with_errors() |
           peeking_sentence_processor_with_errors();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.process('Z');
  ASSERT_THROW(get_value_or_throw(p()), processor_unexpected_input);
  while (p) sentences.push_back(get_value_or_throw(p()));
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeWithErrorsTest, ResetSentence) {
  const char wont_see[] = "C\0011;C\4oops;";
  const char input[] = "C\4STOP;C\3hi5;C\5world;C\4STOP;P\13;C\1u;C\5there;";
  auto p = peek_machine_processor_with_errors() |
           peeking_sentence_processor_with_errors();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.reset();
  while (p) sentences.push_back(get_value_or_throw(p()));
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}

TEST(ProcessorPeekComposeWithErrorsTest, ErrorInSentence) {
  const char wont_see[] = "C\0011;C\5ERROR;C\4oops";
  const char input[] = "C\4STOP;C\3hi5;C\5world;C\4STOP;P\13;C\1u;C\5there;";
  auto p = peek_machine_processor_with_errors() |
           peeking_sentence_processor_with_errors();
  std::vector<std::vector<std::string>> sentences;
  for (const char* c = wont_see; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.process(';');
  ASSERT_THROW(get_value_or_throw(p()), sentence_unexpected_input);
  while (p) sentences.push_back(get_value_or_throw(p()));
  for (const char* c = input; *c; ++c) {
    p.process(*c);
    while (p) sentences.push_back(get_value_or_throw(p()));
  }
  p.finish();
  while (p) sentences.push_back(get_value_or_throw(p()));

  EXPECT_THAT(sentences, ElementsAre(ElementsAre("hi5", "world"),
                                     ElementsAre("r", "u", "there")));
}
}  // namespace
}  // namespace emil::processor::testing
