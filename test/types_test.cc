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

#include "emil/types.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <functional>
#include <initializer_list>
#include <utility>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/string.h"
#include "testing/test_util.h"

namespace emil::typing::testing {

using emil::testing::TestContext;

using ::testing::Eq;
using ::testing::ExplainMatchResult;
using ::testing::PrintToString;

MATCHER_P3(PrintsCorrectly, tc, no, yes,
           "prints as " + PrintToString(no) + " when not canonicalized and " +
               PrintToString(yes) + " when canonicalized") {
  TypePtr t1 =
      tc.get().root.add_root(make_managed<TypeWithAgeRestriction>(arg, 0));
  const auto rn = print_type(arg, CanonicalizeUndeterminedTypes::NO);
  const auto ry = print_type(arg, CanonicalizeUndeterminedTypes::YES);
  const auto rwn = print_type(t1, CanonicalizeUndeterminedTypes::NO);
  const auto rwy = print_type(t1, CanonicalizeUndeterminedTypes::YES);
  *result_listener << "prints as " << PrintToString(rn) << "||"
                   << PrintToString(ry) << "||" << PrintToString(rwn) << "||"
                   << PrintToString(rwy);
  return ExplainMatchResult(Eq(no), rn, result_listener) &&
         ExplainMatchResult(Eq(yes), ry, result_listener) &&
         ExplainMatchResult(Eq(no), rwn, result_listener) &&
         ExplainMatchResult(Eq(yes), rwy, result_listener);
}

TEST(PrintTypeTest, BasicOperation) {
  TestContext tc;
  StampGenerator stamper;

  TypePtr a = tc.root.add_root(make_managed<TypeVar>(u8"'a"));
  EXPECT_THAT(a, PrintsCorrectly(std::ref(tc), u8"'a", u8"'a"));

  TypePtr b = tc.root.add_root(make_managed<TypeVar>(u8"'b"));
  EXPECT_THAT(b, PrintsCorrectly(std::ref(tc), u8"'b", u8"'b"));

  TypePtr ut1 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
  EXPECT_THAT(ut1, PrintsCorrectly(std::ref(tc), u8"'~1", u8"'~0"));

  TypePtr ut2 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
  EXPECT_THAT(ut2, PrintsCorrectly(std::ref(tc), u8"'~2", u8"'~0"));

  TypePtr int_type;
  {
    auto hold = tc.mgr.acquire_hold();
    int_type = tc.root.add_root(make_managed<ConstructedType>(
        make_managed<TypeName>(u8"int", stamper, 0),
        collections::make_array<Type>({})));
  }
  EXPECT_THAT(int_type, PrintsCorrectly(std::ref(tc), u8"int", u8"int"));

  auto list_name =
      tc.root.add_root(make_managed<TypeName>(u8"list", stamper, 1));
  TypePtr list_int_type, list_ut2_type, list_list_ut2_type;
  {
    auto hold = tc.mgr.acquire_hold();
    list_int_type = tc.root.add_root(make_managed<ConstructedType>(
        list_name, collections::make_array({int_type})));
    list_ut2_type = tc.root.add_root(make_managed<ConstructedType>(
        list_name, collections::make_array({ut2})));
    list_list_ut2_type = tc.root.add_root(make_managed<ConstructedType>(
        list_name, collections::make_array({list_ut2_type})));
  }
  EXPECT_THAT(list_int_type,
              PrintsCorrectly(std::ref(tc), u8"int list", u8"int list"));
  EXPECT_THAT(list_ut2_type,
              PrintsCorrectly(std::ref(tc), u8"'~2 list", u8"'~0 list"));
  EXPECT_THAT(
      list_list_ut2_type,
      PrintsCorrectly(std::ref(tc), u8"'~2 list list", u8"'~0 list list"));

  auto pair_name =
      tc.root.add_root(make_managed<TypeName>(u8"pair", stamper, 2));
  TypePtr pair_int_int_type, pair_ut2_ut1_type, pair_a_ut1_type,
      pair_list_list_ut2_b_type;
  {
    auto hold = tc.mgr.acquire_hold();
    pair_int_int_type = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, collections::make_array({int_type, int_type})));
    pair_ut2_ut1_type = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, collections::make_array({ut2, ut1})));
    pair_a_ut1_type = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, collections::make_array({a, ut1})));
    pair_list_list_ut2_b_type = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, collections::make_array({list_list_ut2_type, b})));
  }
  EXPECT_THAT(
      pair_int_int_type,
      PrintsCorrectly(std::ref(tc), u8"(int, int) pair", u8"(int, int) pair"));
  EXPECT_THAT(
      pair_ut2_ut1_type,
      PrintsCorrectly(std::ref(tc), u8"('~2, '~1) pair", u8"('~0, '~1) pair"));
  EXPECT_THAT(pair_a_ut1_type, PrintsCorrectly(std::ref(tc), u8"('a, '~1) pair",
                                               u8"('a, '~0) pair"));
  EXPECT_THAT(pair_list_list_ut2_b_type,
              PrintsCorrectly(std::ref(tc), u8"('~2 list list, 'b) pair",
                              u8"('~0 list list, 'b) pair"));

  TypePtr tuple0, tuple_ut2_ut1, tuple_pair_ut2_ut1_a_ut2;
  {
    auto hold = tc.mgr.acquire_hold();
    tuple0 = tc.root.add_root(
        make_managed<TupleType>(collections::make_array<Type>({})));
    tuple_ut2_ut1 = tc.root.add_root(
        make_managed<TupleType>(collections::make_array({ut2, ut1})));
    tuple_pair_ut2_ut1_a_ut2 = tc.root.add_root(make_managed<TupleType>(
        collections::make_array({pair_ut2_ut1_type, a, ut2})));
  }
  EXPECT_THAT(tuple0, PrintsCorrectly(std::ref(tc), u8"()", u8"()"));
  EXPECT_THAT(tuple_ut2_ut1,
              PrintsCorrectly(std::ref(tc), u8"('~2 * '~1)", u8"('~0 * '~1)"));
  EXPECT_THAT(tuple_pair_ut2_ut1_a_ut2,
              PrintsCorrectly(std::ref(tc), u8"(('~2, '~1) pair * 'a * '~2)",
                              u8"(('~0, '~1) pair * 'a * '~0)"));

  TypePtr record0, record0w, record_ut2, record_ut2w, record_ut2_ut1,
      record_ut2_ut1w, record_ut2_tuple_ut2_ut1_a_ut2_list_int;
  {
    auto hold = tc.mgr.acquire_hold();
    record0 = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map<ManagedString, Type>({})));
    record0w = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map<ManagedString, Type>({}), true));
    record_ut2 = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map({std::make_pair(make_string(u8"k0"), ut2)})));
    record_ut2w = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map({std::make_pair(make_string(u8"k0"), ut2)}),
        true));
    record_ut2_ut1 = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map({std::make_pair(make_string(u8"k0"), ut2),
                                  std::make_pair(make_string(u8"k1"), ut1)})));
    record_ut2_ut1w = tc.root.add_root(make_managed<RecordType>(
        collections::managed_map({std::make_pair(make_string(u8"k0"), ut2),
                                  std::make_pair(make_string(u8"k1"), ut1)}),
        true));
    record_ut2_tuple_ut2_ut1_a_ut2_list_int =
        tc.root.add_root(make_managed<RecordType>(collections::managed_map(
            {std::make_pair(make_string(u8"k0"), ut2),
             std::make_pair(make_string(u8"k1"), tuple_ut2_ut1),
             std::make_pair(make_string(u8"k2"), a),
             std::make_pair(make_string(u8"k3"), ut2),
             std::make_pair(make_string(u8"k4"), list_int_type)})));
  }
  EXPECT_THAT(record0, PrintsCorrectly(std::ref(tc), u8"{}", u8"{}"));
  EXPECT_THAT(record0w, PrintsCorrectly(std::ref(tc), u8"{...}", u8"{...}"));
  EXPECT_THAT(record_ut2,
              PrintsCorrectly(std::ref(tc), u8"{k0: '~2}", u8"{k0: '~0}"));
  EXPECT_THAT(record_ut2w, PrintsCorrectly(std::ref(tc), u8"{k0: '~2, ...}",
                                           u8"{k0: '~0, ...}"));
  EXPECT_THAT(record_ut2_ut1,
              PrintsCorrectly(std::ref(tc), u8"{k0: '~2, k1: '~1}",
                              u8"{k0: '~0, k1: '~1}"));
  EXPECT_THAT(record_ut2_ut1w,
              PrintsCorrectly(std::ref(tc), u8"{k0: '~2, k1: '~1, ...}",
                              u8"{k0: '~0, k1: '~1, ...}"));
  EXPECT_THAT(
      record_ut2_tuple_ut2_ut1_a_ut2_list_int,
      PrintsCorrectly(
          std::ref(tc),
          u8"{k0: '~2, k1: ('~2 * '~1), k2: 'a, k3: '~2, k4: int list}",
          u8"{k0: '~0, k1: ('~0 * '~1), k2: 'a, k3: '~0, k4: int list}"));

  TypePtr fun_ut2_to_ut1 =
      tc.root.add_root(make_managed<FunctionType>(ut2, ut1));
  EXPECT_THAT(fun_ut2_to_ut1,
              PrintsCorrectly(std::ref(tc), u8"'~2 -> '~1", u8"'~0 -> '~1"));
  TypePtr fun_b_to_record0w =
      tc.root.add_root(make_managed<FunctionType>(b, record0w));
  EXPECT_THAT(fun_b_to_record0w,
              PrintsCorrectly(std::ref(tc), u8"'b -> {...}", u8"'b -> {...}"));
  TypePtr fun_list_int_to_ut1 =
      tc.root.add_root(make_managed<FunctionType>(list_int_type, ut1));
  EXPECT_THAT(
      fun_list_int_to_ut1,
      PrintsCorrectly(std::ref(tc), u8"int list -> '~1", u8"int list -> '~0"));
  TypePtr fun_tuple_ut2_ut1_to_ut1 =
      tc.root.add_root(make_managed<FunctionType>(tuple_ut2_ut1, ut1));
  EXPECT_THAT(fun_tuple_ut2_ut1_to_ut1,
              PrintsCorrectly(std::ref(tc), u8"('~2 * '~1) -> '~1",
                              u8"('~0 * '~1) -> '~1"));
}

}  // namespace emil::typing::testing
