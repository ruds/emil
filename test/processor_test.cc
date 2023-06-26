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
#include <string>
#include <vector>

namespace emil::processor::testing {
namespace {

using ::testing::ElementsAre;

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

}  // namespace
}  // namespace emil::processor::testing
