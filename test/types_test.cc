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
#include <string_view>
#include <utility>

#include "emil/collections.h"
#include "emil/gc.h"
#include "emil/string.h"
#include "testing/test_util.h"

namespace emil::typing::testing {

using collections::make_array;
using collections::managed_map;
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

MATCHER_P(PrintsAs, expected, "") {
  auto s = print_type(arg, CanonicalizeUndeterminedTypes::YES);
  *result_listener << "prints as " << PrintToString(s);
  return ExplainMatchResult(Eq(expected), s, result_listener);
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

// Requires a gc hold.
TypePtr apply_two_substitutions(TypePtr t, Substitutions first,
                                Substitutions second) {
  return apply_substitutions(apply_substitutions(t, first), second);
}

TEST(ApplySubstitutionsTest, BasicOperation) {
  TestContext tc;
  StampGenerator stamper;

  const auto int_name =
      tc.root.add_root(make_managed<TypeName>(u8"int", stamper, 0));
  const auto list_name =
      tc.root.add_root(make_managed<TypeName>(u8"list", stamper, 1));
  const auto ut1 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
  const auto ut2 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
  const auto pair_name =
      tc.root.add_root(make_managed<TypeName>(u8"pair", stamper, 2));
  const auto ut3 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
  const auto ut4 = tc.root.add_root(make_managed<UndeterminedType>(stamper));

  TypePtr a = tc.root.add_root(make_managed<TypeVar>(u8"'a"));
  TypePtr b = tc.root.add_root(make_managed<TypeVar>(u8"'b"));
  TypePtr int_type, list_int, list_ut2, list_ut3, list_list_ut3,
      pair_list_ut2_and_int, pair_list_list_ut3_and_int,
      pair_pair_list_list_ut3_and_int_and_list_int, tuple0,
      tuple_pair_list_ut2_and_int_with_tuple0, tuple_list_list_ut3_and_int,
      record0, record0w, record_ut2, record_ut2w,
      record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
      fun_ut3_to_ut1, fun_b_to_record_ut2w,
      fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int;
  {
    auto hold = tc.mgr.acquire_hold();
    int_type = tc.root.add_root(
        make_managed<ConstructedType>(int_name, make_array<Type>({})));
    list_int = tc.root.add_root(
        make_managed<ConstructedType>(list_name, make_array({int_type})));
    list_ut2 = tc.root.add_root(
        make_managed<ConstructedType>(list_name, make_array<Type>({ut2})));
    list_ut3 = tc.root.add_root(
        make_managed<ConstructedType>(list_name, make_array<Type>({ut3})));
    list_list_ut3 = tc.root.add_root(
        make_managed<ConstructedType>(list_name, make_array({list_ut3})));
    pair_list_ut2_and_int = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, make_array({list_ut2, int_type})));
    pair_list_list_ut3_and_int = tc.root.add_root(make_managed<ConstructedType>(
        pair_name, make_array({list_list_ut3, int_type})));
    pair_pair_list_list_ut3_and_int_and_list_int =
        tc.root.add_root(make_managed<ConstructedType>(
            pair_name, make_array({pair_list_list_ut3_and_int, list_int})));
    tuple0 = tc.root.add_root(make_managed<TupleType>(make_array<Type>({})));
    tuple_pair_list_ut2_and_int_with_tuple0 = tc.root.add_root(
        make_managed<TupleType>(make_array({pair_list_ut2_and_int, tuple0})));
    tuple_list_list_ut3_and_int = tc.root.add_root(
        make_managed<TupleType>(make_array({list_list_ut3, int_type})));
    record0 = tc.root.add_root(
        make_managed<RecordType>(managed_map<ManagedString, Type>({})));
    record0w = tc.root.add_root(
        make_managed<RecordType>(managed_map<ManagedString, Type>({}), true));
    record_ut2 = tc.root.add_root(
        make_managed<RecordType>(managed_map<ManagedString, Type>(
            {std::make_pair(make_string(u8"k0"), ut2)})));
    record_ut2w = tc.root.add_root(make_managed<RecordType>(
        managed_map<ManagedString, Type>(
            {std::make_pair(make_string(u8"k0"), ut2)}),
        true));
    record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3 =
        tc.root.add_root(
            make_managed<RecordType>(managed_map<ManagedString, Type>(
                {std::make_pair(make_string(u8"k0"), ut2),
                 std::make_pair(make_string(u8"k1"),
                                tuple_list_list_ut3_and_int),
                 std::make_pair(make_string(u8"k2"), list_list_ut3)})));
    fun_ut3_to_ut1 = tc.root.add_root(make_managed<FunctionType>(ut3, ut1));
    fun_b_to_record_ut2w =
        tc.root.add_root(make_managed<FunctionType>(b, record_ut2w));
    fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int =
        tc.root.add_root(make_managed<FunctionType>(
            list_list_ut3, pair_pair_list_list_ut3_and_int_and_list_int));
  }

  Substitutions sub_empty, sub_ut1_is_list_int,
      sub_ut1_is_list_int_also_ut2_is_list_list_ut3,
      sub_ut1_is_pair_list_ut2_and_int, sub_ut3_is_pair_list_ut2_and_int,
      sub_ut1_is_ut3, sub_ut1_is_b, sub_ut3_is_int;
  {
    auto hold = tc.mgr.acquire_hold();
    sub_empty = tc.root.add_root(managed_map<Stamp, Type>({}));
    sub_ut1_is_list_int =
        tc.root.add_root(sub_empty->insert(ut1->stamp(), list_int).first);
    sub_ut1_is_list_int_also_ut2_is_list_list_ut3 = tc.root.add_root(
        sub_ut1_is_list_int->insert(ut2->stamp(), list_list_ut3).first);
    sub_ut1_is_pair_list_ut2_and_int = tc.root.add_root(
        sub_empty->insert(ut1->stamp(), pair_list_ut2_and_int).first);
    sub_ut3_is_pair_list_ut2_and_int = tc.root.add_root(
        sub_empty->insert(ut3->stamp(), pair_list_ut2_and_int).first);
    sub_ut1_is_ut3 =
        tc.root.add_root(sub_empty->insert(ut1->stamp(), ut3).first);
    sub_ut1_is_b = tc.root.add_root(sub_empty->insert(ut1->stamp(), b).first);
    sub_ut3_is_int =
        tc.root.add_root(sub_empty->insert(ut3->stamp(), int_type).first);
  }

  auto hold = tc.mgr.acquire_hold();

  EXPECT_THAT(apply_substitutions(a, sub_empty), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_empty), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_empty), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_empty), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_empty), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_empty), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub_empty),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub_empty),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub_empty),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_empty),
              PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_empty), PrintsAs(u8"()"));
  EXPECT_THAT(
      apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub_empty),
      PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub_empty),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_empty), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_empty), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_empty),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub_empty),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_empty),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub_empty),
              PrintsAs(u8"'~0 -> '~1"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub_empty),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_empty),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut1_is_list_int), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut1_is_list_int), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut1_is_list_int),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut1_is_list_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut1_is_list_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut1_is_list_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub_ut1_is_list_int),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub_ut1_is_list_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_list_list_ut3_and_int, sub_ut1_is_list_int),
      PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_ut1_is_list_int),
              PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut1_is_list_int),
              PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut1_is_list_int),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(
      apply_substitutions(tuple_list_list_ut3_and_int, sub_ut1_is_list_int),
      PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut1_is_list_int),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut1_is_list_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut1_is_list_int),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub_ut1_is_list_int),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_list_int),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub_ut1_is_list_int),
              PrintsAs(u8"'~0 -> int list"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub_ut1_is_list_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_list_int),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(
      apply_substitutions(a, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"'a"));
  EXPECT_THAT(
      apply_substitutions(b, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(
                  int_type, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(
                  list_int, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(
                  list_ut2, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"'~0 list list list"));
  EXPECT_THAT(apply_substitutions(
                  list_ut3, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(
                  list_list_ut3, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(
      apply_substitutions(pair_list_ut2_and_int,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"('~0 list list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_list_list_ut3_and_int,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(
                  tuple0, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"()"));
  EXPECT_THAT(
      apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"(('~0 list list list, int) pair * ())"));
  EXPECT_THAT(
      apply_substitutions(tuple_list_list_ut3_and_int,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(
                  record0, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(
                  record0w, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(
                  record_ut2, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"{k0: '~0 list list}"));
  EXPECT_THAT(apply_substitutions(
                  record_ut2w, sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
              PrintsAs(u8"{k0: '~0 list list, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"{k0: '~0 list list, k1: ('~0 list list * int), k2: '~0 list "
               u8"list}"));
  EXPECT_THAT(
      apply_substitutions(fun_ut3_to_ut1,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"'~0 -> int list"));
  EXPECT_THAT(
      apply_substitutions(fun_b_to_record_ut2w,
                          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(u8"'b -> {k0: '~0 list list, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_list_int_also_ut2_is_list_list_ut3),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(
      apply_substitutions(list_list_ut3, sub_ut1_is_pair_list_ut2_and_int),
      PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(
      apply_substitutions(record_ut2w, sub_ut1_is_pair_list_ut2_and_int),
      PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_pair_list_ut2_and_int),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THROW(
      apply_substitutions(fun_ut3_to_ut1, sub_ut1_is_pair_list_ut2_and_int),
      UnificationError);
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w,
                                  sub_ut1_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_pair_list_ut2_and_int),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair list"));
  EXPECT_THAT(
      apply_substitutions(list_list_ut3, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"('~0 list, int) pair list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int,
                                  sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int,
                                  sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"(('~0 list, int) pair list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                          sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(
          u8"((('~0 list, int) pair list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int,
                                  sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"(('~0 list, int) pair list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(
      apply_substitutions(record_ut2w, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"{k0: '~0, k1: (('~0 list, int) pair list list * int), k2: "
               u8"('~0 list, int) pair list list}"));
  EXPECT_THAT(
      apply_substitutions(fun_ut3_to_ut1, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"('~0 list, int) pair -> '~1"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w,
                                  sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"('~0 list, int) pair list list -> ((('~0 list, int) pair "
               u8"list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut1_is_ut3), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut1_is_ut3), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut1_is_ut3), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut1_is_ut3),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut1_is_ut3),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut1_is_ut3),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub_ut1_is_ut3),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub_ut1_is_ut3),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub_ut1_is_ut3),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_ut1_is_ut3),
              PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut1_is_ut3), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut1_is_ut3),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub_ut1_is_ut3),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut1_is_ut3), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut1_is_ut3),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut1_is_ut3),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub_ut1_is_ut3),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_ut3),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub_ut1_is_ut3),
              PrintsAs(u8"'~0 -> '~0"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub_ut1_is_ut3),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_ut3),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut1_is_b), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut1_is_b), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut1_is_b), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut1_is_b),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut1_is_b),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut1_is_b),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub_ut1_is_b),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub_ut1_is_b),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub_ut1_is_b),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_ut1_is_b),
              PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut1_is_b), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut1_is_b),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub_ut1_is_b),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut1_is_b), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut1_is_b), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut1_is_b),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub_ut1_is_b),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_b),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub_ut1_is_b),
              PrintsAs(u8"'~0 -> 'b"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub_ut1_is_b),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_b),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_substitutions(a, sub_ut3_is_int), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub_ut3_is_int), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub_ut3_is_int), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub_ut3_is_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub_ut3_is_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub_ut3_is_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub_ut3_is_int),
              PrintsAs(u8"int list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub_ut3_is_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub_ut3_is_int),
              PrintsAs(u8"(int list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                                  sub_ut3_is_int),
              PrintsAs(u8"((int list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub_ut3_is_int), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                  sub_ut3_is_int),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub_ut3_is_int),
              PrintsAs(u8"(int list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub_ut3_is_int), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub_ut3_is_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub_ut3_is_int),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub_ut3_is_int),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut3_is_int),
      PrintsAs(u8"{k0: '~0, k1: (int list list * int), k2: int list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub_ut3_is_int),
              PrintsAs(u8"int -> '~0"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub_ut3_is_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut3_is_int),
      PrintsAs(
          u8"int list list -> ((int list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_two_substitutions(a, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"'a"));
  EXPECT_THAT(apply_two_substitutions(b, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"'b"));
  EXPECT_THAT(apply_two_substitutions(int_type, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_two_substitutions(list_int, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_two_substitutions(list_ut2, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_two_substitutions(list_ut3, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(
      apply_two_substitutions(list_list_ut3, sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"int list list"));
  EXPECT_THAT(apply_two_substitutions(pair_list_ut2_and_int, sub_ut1_is_ut3,
                                      sub_ut3_is_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_two_substitutions(pair_list_list_ut3_and_int,
                                      sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"(int list list, int) pair"));
  EXPECT_THAT(
      apply_two_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                              sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"((int list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_two_substitutions(tuple0, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"()"));
  EXPECT_THAT(apply_two_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                                      sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_two_substitutions(tuple_list_list_ut3_and_int,
                                      sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"(int list list * int)"));
  EXPECT_THAT(apply_two_substitutions(record0, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_two_substitutions(record0w, sub_ut1_is_ut3, sub_ut3_is_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(
      apply_two_substitutions(record_ut2, sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(
      apply_two_substitutions(record_ut2w, sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_two_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"{k0: '~0, k1: (int list list * int), k2: int list list}"));
  EXPECT_THAT(
      apply_two_substitutions(fun_ut3_to_ut1, sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(u8"int -> int"));
  EXPECT_THAT(apply_two_substitutions(fun_b_to_record_ut2w, sub_ut1_is_ut3,
                                      sub_ut3_is_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_two_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_ut3, sub_ut3_is_int),
      PrintsAs(
          u8"int list list -> ((int list list, int) pair, int list) pair"));

  EXPECT_THAT(apply_two_substitutions(a, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'a"));
  EXPECT_THAT(apply_two_substitutions(b, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b"));
  EXPECT_THAT(apply_two_substitutions(int_type, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"int"));
  EXPECT_THAT(apply_two_substitutions(list_int, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"int list"));
  EXPECT_THAT(apply_two_substitutions(list_ut2, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_two_substitutions(list_ut3, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair list"));
  EXPECT_THAT(apply_two_substitutions(list_list_ut3, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair list list"));
  EXPECT_THAT(apply_two_substitutions(pair_list_ut2_and_int, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(
      apply_two_substitutions(pair_list_list_ut3_and_int, sub_ut1_is_ut3,
                              sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"(('~0 list, int) pair list list, int) pair"));
  EXPECT_THAT(
      apply_two_substitutions(pair_pair_list_list_ut3_and_int_and_list_int,
                              sub_ut1_is_ut3, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(
          u8"((('~0 list, int) pair list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_two_substitutions(tuple0, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"()"));
  EXPECT_THAT(
      apply_two_substitutions(tuple_pair_list_ut2_and_int_with_tuple0,
                              sub_ut1_is_ut3, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(
      apply_two_substitutions(tuple_list_list_ut3_and_int, sub_ut1_is_ut3,
                              sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"(('~0 list, int) pair list list * int)"));
  EXPECT_THAT(apply_two_substitutions(record0, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{}"));
  EXPECT_THAT(apply_two_substitutions(record0w, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_two_substitutions(record_ut2, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_two_substitutions(record_ut2w, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_two_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3,
          sub_ut1_is_ut3, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"{k0: '~0, k1: (('~0 list, int) pair list list * int), k2: "
               u8"('~0 list, int) pair list list}"));
  EXPECT_THROW(apply_two_substitutions(fun_ut3_to_ut1, sub_ut1_is_ut3,
                                       sub_ut3_is_pair_list_ut2_and_int),
               UnificationError);
  EXPECT_THAT(apply_two_substitutions(fun_b_to_record_ut2w, sub_ut1_is_ut3,
                                      sub_ut3_is_pair_list_ut2_and_int),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_two_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub_ut1_is_ut3, sub_ut3_is_pair_list_ut2_and_int),
      PrintsAs(u8"('~0 list, int) pair list list -> ((('~0 list, int) pair "
               u8"list list, int) pair, int list) pair"));
}

class UnifyTest : public ::testing::Test {
 protected:
  TestContext tc;
  StampGenerator stamper;

  TypePtr int_type;
  TypePtr float_type;
  managed_ptr<TypeName> list_name;

  // "Early" undetermined types -- older than `pair`.
  managed_ptr<UndeterminedType> ute1;
  managed_ptr<UndeterminedType> ute2;
  managed_ptr<UndeterminedType> ute3;
  managed_ptr<UndeterminedType> ute4;

  managed_ptr<TypeName> pair_name;

  // "Late" undetermined types -- newer than `pair`.
  managed_ptr<UndeterminedType> utl1;
  managed_ptr<UndeterminedType> utl2;
  managed_ptr<UndeterminedType> utl3;
  managed_ptr<UndeterminedType> utl4;

  TypePtr a;  // type variable
  TypePtr b;  // type variable

  TypePtr type_variable(std::u8string_view name) {
    return tc.root.add_root(make_managed<TypeVar>(name));
  }

  TypePtr tuple_type(std::initializer_list<TypePtr> types) {
    auto hold = tc.mgr.acquire_hold();
    return tc.root.add_root(
        make_managed<TupleType>(collections::make_array(types)));
  }

  TypePtr record_type(
      std::initializer_list<std::pair<std::u8string_view, TypePtr>> rows,
      bool has_wildcard = false) {
    auto hold = tc.mgr.acquire_hold();
    auto m = collections::managed_map<ManagedString, Type>({});
    for (const auto& r : rows) {
      m = m->insert(make_string(r.first), r.second).first;
    }
    return tc.root.add_root(make_managed<RecordType>(m, has_wildcard));
  }

  TypePtr function_type(TypePtr param, TypePtr result) {
    return tc.root.add_root(make_managed<FunctionType>(param, result));
  }

  managed_ptr<TypeName> type_name(std::u8string_view name, std::size_t arity) {
    return tc.root.add_root(make_managed<TypeName>(name, stamper, arity));
  }

  TypePtr constructed_type(managed_ptr<TypeName> name,
                           std::initializer_list<TypePtr> types) {
    auto hold = tc.mgr.acquire_hold();
    return tc.root.add_root(
        make_managed<ConstructedType>(name, make_array(types)));
  }

  /** Creates a constructed type with a fresh name. */
  TypePtr constructed_type(std::u8string_view name,
                           std::initializer_list<TypePtr> types) {
    auto hold = tc.mgr.acquire_hold();
    return tc.root.add_root(make_managed<ConstructedType>(
        type_name(name, types.size()), make_array(types)));
  }

  TypePtr list_type(TypePtr el_type) {
    return constructed_type(list_name, {el_type});
  }

  TypePtr pair_type(TypePtr first, TypePtr second) {
    return constructed_type(pair_name, {first, second});
  }

  void SetUp() override {
    int_type = constructed_type(u8"int", {});
    float_type = constructed_type(u8"float", {});
    list_name = type_name(u8"list", 1);
    ute1 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    ute2 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    ute3 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    ute4 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    pair_name = type_name(u8"pair", 2);
    utl1 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    utl2 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    utl3 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    utl4 = tc.root.add_root(make_managed<UndeterminedType>(stamper));
    a = type_variable(u8"'a");
    b = type_variable(u8"'b");
  }
};

TEST_F(UnifyTest, TypeVar) {
  EXPECT_THAT(unify(a, a), PrintsAs(u8"'a"));
  EXPECT_THAT(unify(b, b), PrintsAs(u8"'b"));
  EXPECT_THROW(unify(a, b), UnificationError);

  EXPECT_THAT(unify(a, ute1), PrintsAs(u8"'a"));
  EXPECT_THAT(unify(a, utl1), PrintsAs(u8"'a"));

  EXPECT_THROW(unify(a, tuple_type({})), UnificationError);
  EXPECT_THROW(unify(a, record_type({}, true)), UnificationError);
  EXPECT_THROW(unify(a, function_type(ute1, ute2)), UnificationError);
  EXPECT_THROW(unify(a, list_type(ute1)), UnificationError);
}

TEST_F(UnifyTest, Tuple) {
  const auto t_empty = tuple_type({});
  const auto t_int_list_and_ute1 = tuple_type({list_type(int_type), ute1});
  const auto t_int_list_and_ute1_and_int =
      tuple_type({list_type(int_type), ute1, int_type});
  const auto t_ute2_and_ute3 = tuple_type({ute2, ute3});

  auto hold = tc.mgr.acquire_hold();
  EXPECT_THAT(unify(t_empty, t_empty), PrintsAs(u8"()"));
  EXPECT_THAT(unify(t_empty, ute4), PrintsAs(u8"()"));
  EXPECT_THAT(unify(t_empty, utl1), PrintsAs(u8"()"));

  EXPECT_THAT(unify(t_int_list_and_ute1, t_int_list_and_ute1),
              PrintsAs(u8"(int list * '~0)"));
  EXPECT_THAT(unify(t_int_list_and_ute1, ute4), PrintsAs(u8"(int list * '~0)"));
  EXPECT_THAT(unify(t_int_list_and_ute1, utl1), PrintsAs(u8"(int list * '~0)"));

  EXPECT_THAT(unify(t_int_list_and_ute1_and_int, t_int_list_and_ute1_and_int),
              PrintsAs(u8"(int list * '~0 * int)"));
  EXPECT_THAT(unify(t_int_list_and_ute1_and_int, ute4),
              PrintsAs(u8"(int list * '~0 * int)"));
  EXPECT_THAT(unify(t_int_list_and_ute1_and_int, utl1),
              PrintsAs(u8"(int list * '~0 * int)"));

  EXPECT_THAT(unify(t_ute2_and_ute3, t_ute2_and_ute3),
              PrintsAs(u8"('~0 * '~1)"));
  EXPECT_THAT(unify(t_ute2_and_ute3, ute4), PrintsAs(u8"('~0 * '~1)"));
  EXPECT_THAT(unify(t_ute2_and_ute3, utl1), PrintsAs(u8"('~0 * '~1)"));

  EXPECT_THROW(unify(t_empty, t_int_list_and_ute1), UnificationError);
  EXPECT_THROW(unify(t_empty, t_int_list_and_ute1_and_int), UnificationError);
  EXPECT_THROW(unify(t_empty, t_ute2_and_ute3), UnificationError);

  EXPECT_THROW(unify(t_int_list_and_ute1, t_empty), UnificationError);
  EXPECT_THROW(unify(t_int_list_and_ute1, t_int_list_and_ute1_and_int),
               UnificationError);
  EXPECT_THAT(unify(t_int_list_and_ute1, t_ute2_and_ute3),
              PrintsAs(u8"(int list * '~0)"));

  EXPECT_THROW(unify(t_ute2_and_ute3, t_empty), UnificationError);
  EXPECT_THAT(unify(t_ute2_and_ute3, t_int_list_and_ute1),
              PrintsAs(u8"(int list * '~0)"));
  EXPECT_THROW(unify(t_ute2_and_ute3, t_int_list_and_ute1_and_int),
               UnificationError);

  EXPECT_THROW(unify(t_empty, a), UnificationError);
  EXPECT_THROW(unify(t_empty, record_type({}, true)), UnificationError);
  EXPECT_THROW(unify(t_empty, function_type(ute1, ute2)), UnificationError);
  EXPECT_THROW(unify(t_empty, list_type(ute1)), UnificationError);
}

TEST_F(UnifyTest, Record) {
  const auto r_empty = record_type({});
  const auto rw_empty = record_type({}, true);
  const auto r_1int = record_type({std::make_pair(u8"f1", int_type)});
  const auto rw_1int = record_type({std::make_pair(u8"f1", int_type)}, true);
  const auto r_2float = record_type({std::make_pair(u8"f2", float_type)});
  const auto rw_2float =
      record_type({std::make_pair(u8"f2", float_type)}, true);
  const auto r_1ute1_2ute2 =
      record_type({std::make_pair(u8"f1", ute1), std::make_pair(u8"f2", ute2)});
  const auto rw_1ute1_2ute2 = record_type(
      {std::make_pair(u8"f1", ute1), std::make_pair(u8"f2", ute2)}, true);
  const auto r_2float_3ute3 = record_type(
      {std::make_pair(u8"f2", float_type), std::make_pair(u8"f3", ute3)});
  const auto rw_2float_3ute3 = record_type(
      {std::make_pair(u8"f2", float_type), std::make_pair(u8"f3", ute3)}, true);

  auto hold = tc.mgr.acquire_hold();

  EXPECT_THAT(unify(r_empty, r_empty), PrintsAs(u8"{}"));
  EXPECT_THAT(unify(r_empty, rw_empty), PrintsAs(u8"{}"));
  EXPECT_THAT(unify(rw_empty, r_empty), PrintsAs(u8"{}"));
  EXPECT_THAT(unify(r_empty, ute4), PrintsAs(u8"{}"));
  EXPECT_THAT(unify(r_empty, utl1), PrintsAs(u8"{}"));

  EXPECT_THAT(unify(rw_empty, rw_empty), PrintsAs(u8"{...}"));
  EXPECT_THAT(unify(rw_empty, ute4), PrintsAs(u8"{...}"));
  EXPECT_THAT(unify(rw_empty, utl1), PrintsAs(u8"{...}"));

  EXPECT_THAT(unify(r_1int, r_1int), PrintsAs(u8"{f1: int}"));
  EXPECT_THAT(unify(r_1int, rw_1int), PrintsAs(u8"{f1: int}"));
  EXPECT_THAT(unify(rw_1int, r_1int), PrintsAs(u8"{f1: int}"));
  EXPECT_THAT(unify(r_1int, ute4), PrintsAs(u8"{f1: int}"));
  EXPECT_THAT(unify(r_1int, utl1), PrintsAs(u8"{f1: int}"));

  EXPECT_THAT(unify(rw_1int, rw_1int), PrintsAs(u8"{f1: int, ...}"));
  EXPECT_THAT(unify(rw_1int, ute4), PrintsAs(u8"{f1: int, ...}"));
  EXPECT_THAT(unify(rw_1int, utl1), PrintsAs(u8"{f1: int, ...}"));

  EXPECT_THAT(unify(r_2float, r_2float), PrintsAs(u8"{f2: float}"));
  EXPECT_THAT(unify(r_2float, rw_2float), PrintsAs(u8"{f2: float}"));
  EXPECT_THAT(unify(rw_2float, r_2float), PrintsAs(u8"{f2: float}"));
  EXPECT_THAT(unify(r_2float, ute4), PrintsAs(u8"{f2: float}"));
  EXPECT_THAT(unify(r_2float, utl1), PrintsAs(u8"{f2: float}"));

  EXPECT_THAT(unify(rw_2float, rw_2float), PrintsAs(u8"{f2: float, ...}"));
  EXPECT_THAT(unify(rw_2float, ute4), PrintsAs(u8"{f2: float, ...}"));
  EXPECT_THAT(unify(rw_2float, utl1), PrintsAs(u8"{f2: float, ...}"));

  EXPECT_THAT(unify(r_1ute1_2ute2, r_1ute1_2ute2),
              PrintsAs(u8"{f1: '~0, f2: '~1}"));
  EXPECT_THAT(unify(r_1ute1_2ute2, rw_1ute1_2ute2),
              PrintsAs(u8"{f1: '~0, f2: '~1}"));
  EXPECT_THAT(unify(rw_1ute1_2ute2, r_1ute1_2ute2),
              PrintsAs(u8"{f1: '~0, f2: '~1}"));
  EXPECT_THAT(unify(r_1ute1_2ute2, ute4), PrintsAs(u8"{f1: '~0, f2: '~1}"));
  EXPECT_THAT(unify(r_1ute1_2ute2, utl1), PrintsAs(u8"{f1: '~0, f2: '~1}"));

  EXPECT_THAT(unify(rw_1ute1_2ute2, rw_1ute1_2ute2),
              PrintsAs(u8"{f1: '~0, f2: '~1, ...}"));
  EXPECT_THAT(unify(rw_1ute1_2ute2, ute4),
              PrintsAs(u8"{f1: '~0, f2: '~1, ...}"));
  EXPECT_THAT(unify(rw_1ute1_2ute2, utl1),
              PrintsAs(u8"{f1: '~0, f2: '~1, ...}"));

  EXPECT_THAT(unify(r_2float_3ute3, r_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0}"));
  EXPECT_THAT(unify(r_2float_3ute3, rw_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0}"));
  EXPECT_THAT(unify(rw_2float_3ute3, r_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0}"));
  EXPECT_THAT(unify(r_2float_3ute3, ute4), PrintsAs(u8"{f2: float, f3: '~0}"));
  EXPECT_THAT(unify(r_2float_3ute3, utl1), PrintsAs(u8"{f2: float, f3: '~0}"));

  EXPECT_THAT(unify(rw_2float_3ute3, rw_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0, ...}"));
  EXPECT_THAT(unify(rw_2float_3ute3, ute4),
              PrintsAs(u8"{f2: float, f3: '~0, ...}"));
  EXPECT_THAT(unify(rw_2float_3ute3, utl1),
              PrintsAs(u8"{f2: float, f3: '~0, ...}"));

  EXPECT_THROW(unify(r_empty, r_1int), UnificationError);
  EXPECT_THAT(unify(rw_empty, r_1int), PrintsAs(u8"{f1: int}"));
  EXPECT_THROW(unify(r_empty, rw_1int), UnificationError);
  EXPECT_THAT(unify(rw_empty, rw_1int), PrintsAs(u8"{f1: int, ...}"));

  EXPECT_THROW(unify(r_1int, r_2float), UnificationError);
  EXPECT_THROW(unify(rw_1int, r_2float), UnificationError);
  EXPECT_THROW(unify(r_1int, rw_2float), UnificationError);
  EXPECT_THAT(unify(rw_1int, rw_2float),
              PrintsAs(u8"{f1: int, f2: float, ...}"));

  EXPECT_THROW(unify(r_1int, r_1ute1_2ute2), UnificationError);
  EXPECT_THAT(unify(rw_1int, r_1ute1_2ute2), PrintsAs(u8"{f1: int, f2: '~0}"));
  EXPECT_THROW(unify(r_1int, rw_1ute1_2ute2), UnificationError);
  EXPECT_THAT(unify(rw_1int, rw_1ute1_2ute2),
              PrintsAs(u8"{f1: int, f2: '~0, ...}"));

  EXPECT_THROW(unify(r_2float, r_2float_3ute3), UnificationError);
  EXPECT_THAT(unify(rw_2float, r_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0}"));
  EXPECT_THROW(unify(r_2float, rw_2float_3ute3), UnificationError);
  EXPECT_THAT(unify(rw_2float, rw_2float_3ute3),
              PrintsAs(u8"{f2: float, f3: '~0, ...}"));

  EXPECT_THROW(unify(r_1ute1_2ute2, r_2float_3ute3), UnificationError);
  EXPECT_THROW(unify(rw_1ute1_2ute2, r_2float_3ute3), UnificationError);
  EXPECT_THROW(unify(r_1ute1_2ute2, rw_2float_3ute3), UnificationError);
  EXPECT_THAT(unify(rw_1ute1_2ute2, rw_2float_3ute3),
              PrintsAs(u8"{f1: '~0, f2: float, f3: '~1, ...}"));
}

TEST_F(UnifyTest, Function) {
  const auto int_to_float = function_type(int_type, float_type);
  const auto ute1_to_ute2 = function_type(ute1, ute2);

  auto hold = tc.mgr.acquire_hold();

  EXPECT_THAT(unify(int_to_float, int_to_float), PrintsAs(u8"int -> float"));
  EXPECT_THAT(unify(ute1_to_ute2, ute1_to_ute2), PrintsAs(u8"'~0 -> '~1"));
  EXPECT_THAT(unify(ute1_to_ute2, int_to_float), PrintsAs(u8"int -> float"));
  EXPECT_THAT(unify(int_to_float, ute1_to_ute2), PrintsAs(u8"int -> float"));
}

TEST_F(UnifyTest, Constructed) {
  const auto list_int = list_type(int_type);
  const auto list_ute1 = list_type(ute1);
  const auto list_utl1 = list_type(utl1);
  const auto pair_int_float = pair_type(int_type, float_type);
  const auto pair_ute2_utl2 = pair_type(ute2, utl2);
  const auto list_pair_int_float = list_type(pair_int_float);

  const auto new_pair_name = type_name(u8"pair", 2);
  const auto new_pair_int_float =
      constructed_type(new_pair_name, {int_type, float_type});

  auto hold = tc.mgr.acquire_hold();

  EXPECT_THAT(unify(list_int, list_int), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(list_int, ute4), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(list_int, utl4), PrintsAs(u8"int list"));

  EXPECT_THAT(unify(list_ute1, list_ute1), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(unify(list_ute1, ute4), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(unify(list_ute1, utl4), PrintsAs(u8"'~0 list"));

  EXPECT_THAT(unify(list_utl1, list_ute1), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(unify(list_utl1, ute4), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(unify(list_utl1, utl4), PrintsAs(u8"'~0 list"));

  EXPECT_THAT(unify(pair_int_float, pair_int_float),
              PrintsAs(u8"(int, float) pair"));
  EXPECT_THROW(unify(pair_int_float, ute4), UnificationError);
  EXPECT_THAT(unify(pair_int_float, utl4), PrintsAs(u8"(int, float) pair"));

  EXPECT_THAT(unify(pair_ute2_utl2, pair_ute2_utl2),
              PrintsAs(u8"('~0, '~1) pair"));
  EXPECT_THROW(unify(pair_ute2_utl2, ute4), UnificationError);
  EXPECT_THAT(unify(pair_ute2_utl2, utl4), PrintsAs(u8"('~0, '~1) pair"));

  EXPECT_THAT(unify(list_pair_int_float, list_pair_int_float),
              PrintsAs(u8"(int, float) pair list"));
  EXPECT_THROW(unify(list_pair_int_float, ute4), UnificationError);
  EXPECT_THAT(unify(list_pair_int_float, utl4),
              PrintsAs(u8"(int, float) pair list"));

  EXPECT_THAT(unify(new_pair_int_float, new_pair_int_float),
              PrintsAs(u8"(int, float) pair"));
  EXPECT_THROW(unify(new_pair_int_float, ute4), UnificationError);
  EXPECT_THROW(unify(new_pair_int_float, utl4), UnificationError);

  EXPECT_THAT(unify(list_int, list_ute1), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(list_ute1, list_int), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(list_int, list_utl1), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(list_utl1, list_int), PrintsAs(u8"int list"));

  EXPECT_THAT(unify(pair_int_float, pair_ute2_utl2),
              PrintsAs(u8"(int, float) pair"));
  EXPECT_THAT(unify(pair_ute2_utl2, pair_int_float),
              PrintsAs(u8"(int, float) pair"));
  EXPECT_THROW(unify(pair_int_float, new_pair_int_float), UnificationError);
  EXPECT_THROW(unify(new_pair_int_float, pair_int_float), UnificationError);

  EXPECT_THROW(unify(list_ute1, list_pair_int_float), UnificationError);
  EXPECT_THROW(unify(list_pair_int_float, list_ute1), UnificationError);
  EXPECT_THAT(unify(list_utl1, list_pair_int_float),
              PrintsAs(u8"(int, float) pair list"));
  EXPECT_THAT(unify(list_pair_int_float, list_utl1),
              PrintsAs(u8"(int, float) pair list"));
}

TEST_F(UnifyTest, Undetermined) {
  const auto list_ute1 = list_type(ute1);
  const auto list_utl1 = list_type(utl1);
  const auto pair_int_float = pair_type(int_type, float_type);

  auto hold = tc.mgr.acquire_hold();

  EXPECT_THAT(unify(ute1, a), PrintsAs(u8"'a"));
  EXPECT_THAT(unify(ute1, tuple_type({int_type, float_type})),
              PrintsAs(u8"(int * float)"));
  EXPECT_THAT(unify(ute1, record_type({std::make_pair(u8"f1", int_type)})),
              PrintsAs(u8"{f1: int}"));
  EXPECT_THAT(unify(ute1, function_type(int_type, float_type)),
              PrintsAs(u8"int -> float"));
  EXPECT_THAT(unify(ute1, list_type(int_type)), PrintsAs(u8"int list"));
  EXPECT_THAT(unify(utl1, list_type(int_type)), PrintsAs(u8"int list"));
  EXPECT_THROW(unify(ute1, pair_int_float), UnificationError);
  EXPECT_THAT(unify(utl1, pair_int_float), PrintsAs(u8"(int, float) pair"));

  EXPECT_THAT(unify(ute1, ute1), PrintsAs(u8"'~0"));
  EXPECT_THAT(unify(ute1, ute2), PrintsAs(u8"'~0"));
  EXPECT_THAT(unify(ute2, list_ute1), PrintsAs(u8"'~0 list"));
  EXPECT_THROW(unify(ute1, list_ute1), UnificationError);

  EXPECT_THROW(unify(ute1, pair_int_float), UnificationError);
  EXPECT_THROW(unify(pair_int_float, ute1), UnificationError);
  EXPECT_THAT(unify(utl1, pair_int_float), PrintsAs(u8"(int, float) pair"));
  EXPECT_THAT(unify(pair_int_float, utl1), PrintsAs(u8"(int, float) pair"));

  EXPECT_THAT(unify(tuple_type({ute1, ute2}), tuple_type({ute2, ute1})),
              PrintsAs(u8"('~0 * '~0)"));
  EXPECT_THAT(unify(record_type({std::make_pair(u8"f1", ute1),
                                 std::make_pair(u8"f2", ute2)}),
                    record_type({std::make_pair(u8"f1", ute2),
                                 std::make_pair(u8"f2", ute1)})),
              PrintsAs(u8"{f1: '~0, f2: '~0}"));
  EXPECT_THAT(unify(function_type(ute1, ute2), function_type(ute2, ute1)),
              PrintsAs(u8"'~0 -> '~0"));
  EXPECT_THAT(unify(pair_type(ute1, ute2), pair_type(ute2, ute1)),
              PrintsAs(u8"('~0, '~0) pair"));

  EXPECT_THAT(unify(tuple_type({ute2, list_ute1, ute3}),
                    tuple_type({list_type(ute3), ute2, int_type})),
              PrintsAs(u8"(int list * int list * int)"));

  EXPECT_THAT(
      unify(tuple_type({utl1, utl2}), tuple_type({utl2, pair_int_float})),
      PrintsAs(u8"((int, float) pair * (int, float) pair)"));
  EXPECT_THROW(
      unify(tuple_type({utl1, ute2}), tuple_type({ute2, pair_int_float})),
      UnificationError);
  EXPECT_THROW(
      unify(tuple_type({ute1, utl2}), tuple_type({utl2, pair_int_float})),
      UnificationError);
}

}  // namespace emil::typing::testing
