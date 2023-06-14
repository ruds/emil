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
#include "emil/runtime.h"
#include "emil/string.h"
#include "testing/test_util.h"

namespace emil {
template <typename T>
const T* GetRawPointer(managed_ptr<T> ptr) {
  return &*ptr;
}
}  // namespace emil

namespace emil::typing::testing {

using collections::make_array;
using collections::managed_map;
using emil::testing::TestContext;

using ::testing::Eq;
using ::testing::ExplainMatchResult;
using ::testing::Pointee;
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
  auto hold = ctx().mgr->acquire_hold();
  auto s = print_type(arg, CanonicalizeUndeterminedTypes::YES);
  *result_listener << "prints as " << PrintToString(s);
  return ExplainMatchResult(Eq(expected), s, result_listener);
}

class TypesTestBase : public ::testing::Test {
 protected:
  TestContext tc;
  StampGenerator stamper;

  TypePtr int_type = constructed_type(u8"int", {}, INFINITE_SPAN);
  TypePtr float_type = constructed_type(u8"float", {}, INFINITE_SPAN);
  managed_ptr<TypeName> list_name = type_name(u8"list", 1, 2);

  managed_ptr<TypeVar> type_variable(std::u8string_view name) {
    return tc.root.add_root(make_managed<TypeVar>(name));
  }

  managed_ptr<UndeterminedType> undetermined_type() {
    return tc.root.add_root(make_managed<UndeterminedType>(stamper));
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

  managed_ptr<TypeName> type_name(std::u8string_view name, std::size_t arity,
                                  std::size_t span) {
    return tc.root.add_root(make_managed<TypeName>(name, stamper, arity, span));
  }

  TypePtr constructed_type(managed_ptr<TypeName> name,
                           std::initializer_list<TypePtr> types) {
    auto hold = tc.mgr.acquire_hold();
    return tc.root.add_root(
        make_managed<ConstructedType>(name, make_array(types)));
  }

  /** Creates a constructed type with a fresh name. */
  TypePtr constructed_type(std::u8string_view name,
                           std::initializer_list<TypePtr> types,
                           std::size_t span) {
    auto hold = tc.mgr.acquire_hold();
    return tc.root.add_root(make_managed<ConstructedType>(
        type_name(name, types.size(), span), make_array(types)));
  }

  TypePtr list_type(TypePtr el_type) {
    return constructed_type(list_name, {el_type});
  }
};

using TypeFunctionTest = TypesTestBase;

TEST_F(TypeFunctionTest, Instantiate) {
  // {k0: 'a,
  //  k1: ('b * 'c),
  //  k2: {bar: '~0, foo: 'a, ...} list -> ('b * '~1 * '~2)}
  //
  // with 'a and 'b bound and mapped to int list and '~0 -> 'c,
  // respectively, becomes
  // {k0: int list,
  //  k1: ('~0 -> 'c * 'c),
  //  k2: {bar: '~1, foo: int list, ...} list
  //    -> ('~0 -> 'c * '~2 * '~3)}
  auto hold = tc.mgr.acquire_hold();
  auto a = type_variable(u8"'a");
  auto b = type_variable(u8"'b");
  auto c = type_variable(u8"'c");
  auto ut0 = undetermined_type();
  auto contype = constructed_type(u8"contype", {}, 0);
  auto ut1var = undetermined_type();
  auto ut1 = make_managed<TypeWithAgeRestriction>(ut1var, ut0->stamp()->id());
  auto ut2 = undetermined_type();
  auto ut3 = undetermined_type();

  auto func = make_managed<TypeFunction>(
      record_type(
          {{u8"k0", a},
           {u8"k1", tuple_type({b, c})},
           {u8"k2", function_type(list_type(record_type(
                                      {{u8"bar", ut0}, {u8"foo", a}}, true)),
                                  tuple_type({b, ut1, ut2}))}}),
      make_array({a->name_ptr(), b->name_ptr()}));
  auto instance = func->instantiate(
      make_array({list_type(int_type), function_type(ut3, c)}));

  EXPECT_THAT(
      instance,
      PrintsAs(u8"{k0: int list, k1: (('~0 -> 'c) * 'c), k2: {bar: '~1, foo: "
               u8"int list, ...} list -> (('~0 -> 'c) * '~2 * '~3)}"));
  EXPECT_THROW(apply_substitutions(instance, managed_map<Stamp, Type>(
                                                 {{ut0->stamp(), contype}})),
               UnificationError);
  EXPECT_THROW(apply_substitutions(instance, managed_map<Stamp, Type>(
                                                 {{ut1var->stamp(), contype}})),
               UnificationError);
  EXPECT_NO_THROW(apply_substitutions(
      instance, managed_map<Stamp, Type>({{ut2->stamp(), contype}})));
}

using TypeSchemeTest = TypesTestBase;

TEST_F(TypeSchemeTest, Instantiate) {
  // {k0: 'a,
  //  k1: ('b * 'c),
  //  k2: {bar: '~0, foo: 'a, ...} list -> ('b * '~1 * '~2)}
  //
  // with 'a and 'b bound becomes
  // {k0: '~0,
  //  k1: ('~1 * 'c),
  //  k2: {bar: '~2, foo: '~0, ...} list -> ('~1 * '~3 * '~4)}
  auto hold = tc.mgr.acquire_hold();
  auto a = type_variable(u8"'a");
  auto b = type_variable(u8"'b");
  auto c = type_variable(u8"'c");
  auto ut0 = undetermined_type();
  auto contype = constructed_type(u8"contype", {}, 0);
  auto ut1var = undetermined_type();
  auto ut1 = make_managed<TypeWithAgeRestriction>(ut1var, ut0->stamp()->id());
  auto ut2 = undetermined_type();

  auto scheme = make_managed<TypeScheme>(
      record_type(
          {{u8"k0", a},
           {u8"k1", tuple_type({b, c})},
           {u8"k2", function_type(list_type(record_type(
                                      {{u8"bar", ut0}, {u8"foo", a}}, true)),
                                  tuple_type({b, ut1, ut2}))}}),
      make_array({a->name_ptr(), b->name_ptr()}));
  auto instance = scheme->instantiate(stamper);

  EXPECT_THAT(instance,
              PrintsAs(u8"{k0: '~0, k1: ('~1 * 'c), k2: {bar: '~2, foo: '~0, "
                       u8"...} list -> ('~1 * '~3 * '~4)}"));
  EXPECT_THROW(apply_substitutions(instance, managed_map<Stamp, Type>(
                                                 {{ut0->stamp(), contype}})),
               UnificationError);
  EXPECT_THROW(apply_substitutions(instance, managed_map<Stamp, Type>(
                                                 {{ut1var->stamp(), contype}})),
               UnificationError);
  EXPECT_NO_THROW(apply_substitutions(
      instance, managed_map<Stamp, Type>({{ut2->stamp(), contype}})));
}

TEST_F(TypeSchemeTest, Generalize) {
  // {k0: '~0,
  //  k1: ('~1 * 'b),
  //  k2: {bar: 'd, foo: '~0} list -> ('~1 * 'c * '~2),
  //  k3: 'c -> 'a}
  //
  // with ~1, 'c, and 'd free in the context generalizes to
  //
  // {k0: 'a,
  //  k1: ('~0 * 'b),
  //  k2: {bar: 'd, foo: 'a} list -> ('~0 * 'c * 'e),
  //  k3: 'c -> 'f}
  auto hold = tc.mgr.acquire_hold();

  auto a = type_variable(u8"'a");
  auto b = type_variable(u8"'b");
  auto c = type_variable(u8"'c");
  auto d = type_variable(u8"'d");
  auto ut0 = undetermined_type();
  auto ut1 = undetermined_type();
  auto ut2 = undetermined_type();

  auto type = record_type(
      {{u8"k0", ut0},
       {u8"k1", tuple_type({ut1, b})},
       {u8"k2",
        function_type(list_type(record_type({{u8"bar", d}, {u8"foo", ut0}})),
                      tuple_type({ut1, c, ut2}))},
       {u8"k3", function_type(c, a)}});
  auto C = Context::empty();
  C = C + collections::managed_set({make_string(u8"'c")});
  C = C + (C->env() + C->env()->val_env()->add_binding(
                          u8"foo",
                          make_managed<TypeScheme>(
                              tuple_type({d, ut1}),
                              collections::make_array<ManagedString>({})),
                          IdStatus::Variable, false));
  auto scheme = TypeScheme::generalize(C, type);

  EXPECT_THAT(*scheme->bound(),
              ::testing::ElementsAre(Pointee(Eq(u8"'a")), Pointee(Eq(u8"'b")),
                                     Pointee(Eq(u8"'e")), Pointee(Eq(u8"'f"))));
  EXPECT_THAT(scheme->t(),
              PrintsAs(u8"{k0: 'a, k1: ('~0 * 'b), k2: {bar: 'd, foo: 'a} "
                       u8"list -> ('~0 * 'c * 'e), k3: 'c -> 'f}"));

  EXPECT_THROW(TypeScheme::generalize(C, record_type({{u8"k0", a}}, true)),
               UnificationError);
}

using PrintTypeTest = TypesTestBase;

TEST_F(PrintTypeTest, BasicOperation) {
  TypePtr a = type_variable(u8"'a");
  EXPECT_THAT(a, PrintsCorrectly(std::ref(tc), u8"'a", u8"'a"));

  TypePtr b = type_variable(u8"'b");
  EXPECT_THAT(b, PrintsCorrectly(std::ref(tc), u8"'b", u8"'b"));

  TypePtr ut1 = undetermined_type();
  EXPECT_THAT(ut1, PrintsCorrectly(std::ref(tc), u8"'~4", u8"'~0"));

  TypePtr ut2 = undetermined_type();
  EXPECT_THAT(ut2, PrintsCorrectly(std::ref(tc), u8"'~5", u8"'~0"));

  EXPECT_THAT(int_type, PrintsCorrectly(std::ref(tc), u8"int", u8"int"));

  EXPECT_THAT(list_type(int_type),
              PrintsCorrectly(std::ref(tc), u8"int list", u8"int list"));
  EXPECT_THAT(list_type(ut2),
              PrintsCorrectly(std::ref(tc), u8"'~5 list", u8"'~0 list"));
  EXPECT_THAT(
      list_type(list_type(ut2)),
      PrintsCorrectly(std::ref(tc), u8"'~5 list list", u8"'~0 list list"));

  auto pair_name = type_name(u8"pair", 2, 1);
  EXPECT_THAT(
      constructed_type(pair_name, {int_type, int_type}),
      PrintsCorrectly(std::ref(tc), u8"(int, int) pair", u8"(int, int) pair"));
  EXPECT_THAT(
      constructed_type(pair_name, {ut2, ut1}),
      PrintsCorrectly(std::ref(tc), u8"('~5, '~4) pair", u8"('~0, '~1) pair"));
  EXPECT_THAT(
      constructed_type(pair_name, {a, ut1}),
      PrintsCorrectly(std::ref(tc), u8"('a, '~4) pair", u8"('a, '~0) pair"));
  EXPECT_THAT(constructed_type(pair_name, {list_type(list_type(ut2)), b}),
              PrintsCorrectly(std::ref(tc), u8"('~5 list list, 'b) pair",
                              u8"('~0 list list, 'b) pair"));

  EXPECT_THAT(tuple_type({}), PrintsCorrectly(std::ref(tc), u8"()", u8"()"));
  EXPECT_THAT(tuple_type({ut2, ut1}),
              PrintsCorrectly(std::ref(tc), u8"('~5 * '~4)", u8"('~0 * '~1)"));
  EXPECT_THAT(tuple_type({constructed_type(pair_name, {ut2, ut1}), a, ut2}),
              PrintsCorrectly(std::ref(tc), u8"(('~5, '~4) pair * 'a * '~5)",
                              u8"(('~0, '~1) pair * 'a * '~0)"));

  EXPECT_THAT(record_type({}), PrintsCorrectly(std::ref(tc), u8"{}", u8"{}"));
  EXPECT_THAT(record_type({}, true),
              PrintsCorrectly(std::ref(tc), u8"{...}", u8"{...}"));
  EXPECT_THAT(record_type({{u8"k0", ut2}}),
              PrintsCorrectly(std::ref(tc), u8"{k0: '~5}", u8"{k0: '~0}"));
  EXPECT_THAT(
      record_type({{u8"k0", ut2}}, true),
      PrintsCorrectly(std::ref(tc), u8"{k0: '~5, ...}", u8"{k0: '~0, ...}"));
  EXPECT_THAT(record_type({{u8"k0", ut2}, {u8"k1", ut1}}),
              PrintsCorrectly(std::ref(tc), u8"{k0: '~5, k1: '~4}",
                              u8"{k0: '~0, k1: '~1}"));
  EXPECT_THAT(record_type({{u8"k0", ut2}, {u8"k1", ut1}}, true),
              PrintsCorrectly(std::ref(tc), u8"{k0: '~5, k1: '~4, ...}",
                              u8"{k0: '~0, k1: '~1, ...}"));
  EXPECT_THAT(
      record_type({{u8"k0", ut2},
                   {u8"k1", tuple_type({ut2, ut1})},
                   {u8"k2", a},
                   {u8"k3", ut2},
                   {u8"k4", list_type(int_type)}}),
      PrintsCorrectly(
          std::ref(tc),
          u8"{k0: '~5, k1: ('~5 * '~4), k2: 'a, k3: '~5, k4: int list}",
          u8"{k0: '~0, k1: ('~0 * '~1), k2: 'a, k3: '~0, k4: int list}"));

  EXPECT_THAT(function_type(ut2, ut1),
              PrintsCorrectly(std::ref(tc), u8"'~5 -> '~4", u8"'~0 -> '~1"));
  EXPECT_THAT(function_type(b, record_type({}, true)),
              PrintsCorrectly(std::ref(tc), u8"'b -> {...}", u8"'b -> {...}"));
  EXPECT_THAT(function_type(function_type(ut2, ut1), function_type(a, b)),
              PrintsCorrectly(std::ref(tc), u8"('~5 -> '~4) -> 'a -> 'b",
                              u8"('~0 -> '~1) -> 'a -> 'b"));
  EXPECT_THAT(
      function_type(list_type(int_type), ut1),
      PrintsCorrectly(std::ref(tc), u8"int list -> '~4", u8"int list -> '~0"));
  EXPECT_THAT(function_type(tuple_type({ut2, ut1}), ut1),
              PrintsCorrectly(std::ref(tc), u8"('~5 * '~4) -> '~4",
                              u8"('~0 * '~1) -> '~1"));
}

// Requires a gc hold.
TypePtr apply_two_substitutions(TypePtr t, Substitutions first,
                                Substitutions second) {
  return apply_substitutions(apply_substitutions(t, first), second);
}

class ApplySubstitutionsTest : public TypesTestBase {
 protected:
  managed_ptr<UndeterminedType> ut1 = undetermined_type();
  managed_ptr<UndeterminedType> ut2 = undetermined_type();

  managed_ptr<TypeName> pair_name = type_name(u8"pair", 2, 1);

  managed_ptr<UndeterminedType> ut3 = undetermined_type();
  managed_ptr<UndeterminedType> ut4 = undetermined_type();

  TypePtr a = type_variable(u8"'a");
  TypePtr b = type_variable(u8"'b");

  TypePtr list_int = list_type(int_type);
  TypePtr list_ut2 = list_type(ut2);
  TypePtr list_ut3 = list_type(ut3);
  TypePtr list_list_ut3 = list_type(list_ut3);
  TypePtr pair_list_ut2_and_int = pair_type(list_ut2, int_type);
  TypePtr pair_list_list_ut3_and_int = pair_type(list_list_ut3, int_type);
  TypePtr pair_pair_list_list_ut3_and_int_and_list_int =
      pair_type(pair_list_list_ut3_and_int, list_int);
  TypePtr tuple0 = tuple_type({});
  TypePtr tuple_pair_list_ut2_and_int_with_tuple0 =
      tuple_type({pair_list_ut2_and_int, tuple0});
  TypePtr tuple_list_list_ut3_and_int = tuple_type({list_list_ut3, int_type});
  TypePtr record0 = record_type({});
  TypePtr record0w = record_type({}, true);
  TypePtr record_ut2 = record_type({{u8"k0", ut2}});
  TypePtr record_ut2w = record_type({{u8"k0", ut2}}, true);
  TypePtr record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3 =
      record_type({{u8"k0", ut2},
                   {u8"k1", tuple_list_list_ut3_and_int},
                   {u8"k2", list_list_ut3}});
  TypePtr fun_ut3_to_ut1 = function_type(ut3, ut1);
  TypePtr fun_b_to_record_ut2w = function_type(b, record_ut2w);
  TypePtr fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int =
      function_type(list_list_ut3,
                    pair_pair_list_list_ut3_and_int_and_list_int);

  MemoryManager::hold hold = tc.mgr.acquire_hold();

  TypePtr pair_type(TypePtr a, TypePtr b) {
    return constructed_type(pair_name, {a, b});
  }
};

TEST_F(ApplySubstitutionsTest, EmptySubs) {
  auto sub = managed_map<Stamp, Type>({});

  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"'~0 -> '~1"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, SingleSub) {
  auto sub = managed_map<Stamp, Type>({{ut1->stamp(), list_int}});
  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"'~0 -> int list"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, TwoSubs) {
  auto sub = managed_map<Stamp, Type>(
      {{ut1->stamp(), list_int}, {ut2->stamp(), list_list_ut3}});
  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub),
              PrintsAs(u8"'~0 list list list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list list list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list list list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub),
              PrintsAs(u8"{k0: '~0 list list}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0 list list, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0 list list, k1: ('~0 list list * int), k2: '~0 list "
               u8"list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"'~0 -> int list"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0 list list, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, SubYoungType) {
  auto sub = managed_map<Stamp, Type>({{ut1->stamp(), pair_list_ut2_and_int}});

  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THROW(apply_substitutions(fun_ut3_to_ut1, sub), UnificationError);
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, YoungTypeForYoungVar) {
  auto sub = managed_map<Stamp, Type>({{ut3->stamp(), pair_list_ut2_and_int}});
  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub),
              PrintsAs(u8"('~0 list, int) pair list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"('~0 list, int) pair list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"(('~0 list, int) pair list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(
          u8"((('~0 list, int) pair list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"(('~0 list, int) pair list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: (('~0 list, int) pair list list * int), k2: "
               u8"('~0 list, int) pair list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"('~0 list, int) pair -> '~1"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(u8"('~0 list, int) pair list list -> ((('~0 list, int) pair "
               u8"list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, YoungVariableForOld) {
  auto sub = managed_map<Stamp, Type>({{ut1->stamp(), ut3}});

  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"'~0 -> '~0"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, SubTypeVar) {
  auto sub = managed_map<Stamp, Type>({{ut1->stamp(), b}});

  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"'~0 list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"(('~0 list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"('~0 list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: ('~1 list list * int), k2: '~1 list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"'~0 -> 'b"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"'~0 list list -> (('~0 list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, NewVar) {
  auto sub = managed_map<Stamp, Type>({{ut3->stamp(), int_type}});
  EXPECT_THAT(apply_substitutions(a, sub), PrintsAs(u8"'a"));
  EXPECT_THAT(apply_substitutions(b, sub), PrintsAs(u8"'b"));
  EXPECT_THAT(apply_substitutions(int_type, sub), PrintsAs(u8"int"));
  EXPECT_THAT(apply_substitutions(list_int, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_ut2, sub), PrintsAs(u8"'~0 list"));
  EXPECT_THAT(apply_substitutions(list_ut3, sub), PrintsAs(u8"int list"));
  EXPECT_THAT(apply_substitutions(list_list_ut3, sub),
              PrintsAs(u8"int list list"));
  EXPECT_THAT(apply_substitutions(pair_list_ut2_and_int, sub),
              PrintsAs(u8"('~0 list, int) pair"));
  EXPECT_THAT(apply_substitutions(pair_list_list_ut3_and_int, sub),
              PrintsAs(u8"(int list list, int) pair"));
  EXPECT_THAT(
      apply_substitutions(pair_pair_list_list_ut3_and_int_and_list_int, sub),
      PrintsAs(u8"((int list list, int) pair, int list) pair"));
  EXPECT_THAT(apply_substitutions(tuple0, sub), PrintsAs(u8"()"));
  EXPECT_THAT(apply_substitutions(tuple_pair_list_ut2_and_int_with_tuple0, sub),
              PrintsAs(u8"(('~0 list, int) pair * ())"));
  EXPECT_THAT(apply_substitutions(tuple_list_list_ut3_and_int, sub),
              PrintsAs(u8"(int list list * int)"));
  EXPECT_THAT(apply_substitutions(record0, sub), PrintsAs(u8"{}"));
  EXPECT_THAT(apply_substitutions(record0w, sub), PrintsAs(u8"{...}"));
  EXPECT_THAT(apply_substitutions(record_ut2, sub), PrintsAs(u8"{k0: '~0}"));
  EXPECT_THAT(apply_substitutions(record_ut2w, sub),
              PrintsAs(u8"{k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          record_ut2_plus_tuple_list_list_ut3_and_int_plus_list_list_ut3, sub),
      PrintsAs(u8"{k0: '~0, k1: (int list list * int), k2: int list list}"));
  EXPECT_THAT(apply_substitutions(fun_ut3_to_ut1, sub),
              PrintsAs(u8"int -> '~0"));
  EXPECT_THAT(apply_substitutions(fun_b_to_record_ut2w, sub),
              PrintsAs(u8"'b -> {k0: '~0, ...}"));
  EXPECT_THAT(
      apply_substitutions(
          fun_list_list_ut3_to_pair_pair_list_list_ut3_and_int_and_list_int,
          sub),
      PrintsAs(
          u8"int list list -> ((int list list, int) pair, int list) pair"));
}

TEST_F(ApplySubstitutionsTest, ChainSubs) {
  auto sub_ut1_is_ut3 = managed_map<Stamp, Type>({{ut1->stamp(), ut3}});
  auto sub_ut3_is_int = managed_map<Stamp, Type>({{ut3->stamp(), int_type}});
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
}

TEST_F(ApplySubstitutionsTest, ChainWithYoungTypeName) {
  auto sub_ut1_is_ut3 = managed_map<Stamp, Type>({{ut1->stamp(), ut3}});
  auto sub_ut3_is_pair_list_ut2_and_int =
      managed_map<Stamp, Type>({{ut3->stamp(), pair_list_ut2_and_int}});
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

class UnifyTest : public TypesTestBase {
 protected:
  // "Early" undetermined types -- older than `pair`.
  managed_ptr<UndeterminedType> ute1 = undetermined_type();
  managed_ptr<UndeterminedType> ute2 = undetermined_type();
  managed_ptr<UndeterminedType> ute3 = undetermined_type();
  managed_ptr<UndeterminedType> ute4 = undetermined_type();

  managed_ptr<TypeName> pair_name = type_name(u8"pair", 2, 1);

  // "Late" undetermined types -- newer than `pair`.
  managed_ptr<UndeterminedType> utl1 = undetermined_type();
  managed_ptr<UndeterminedType> utl2 = undetermined_type();
  managed_ptr<UndeterminedType> utl3 = undetermined_type();
  managed_ptr<UndeterminedType> utl4 = undetermined_type();

  TypePtr a = type_variable(u8"'a");
  TypePtr b = type_variable(u8"'b");

  TypePtr unify(TypePtr l, TypePtr r) {
    auto hold = ctx().mgr->acquire_hold();
    Substitutions subs = collections::managed_map<Stamp, Type>({});
    return tc.root.add_root(typing::unify(std::move(l), std::move(r), subs,
                                          NO_ADDITIONAL_TYPE_NAME_RESTRICTION,
                                          NO_ADDITIONAL_TYPE_NAME_RESTRICTION)
                                .unified_type);
  }

  TypePtr pair_type(TypePtr first, TypePtr second) {
    return constructed_type(pair_name, {first, second});
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

  EXPECT_THAT(
      unify(tuple_type({ute1, ute2}), tuple_type({ute3, list_type(ute3)})),
      PrintsAs(u8"('~0 * '~0 list)"));
  EXPECT_THAT(
      unify(tuple_type({ute3, list_type(ute3)}), tuple_type({ute1, ute2})),
      PrintsAs(u8"('~0 * '~0 list)"));
  EXPECT_THAT(
      unify(tuple_type({ute2, ute3}), tuple_type({ute1, list_type(ute1)})),
      PrintsAs(u8"('~0 * '~0 list)"));
  EXPECT_THAT(
      unify(tuple_type({ute1, list_type(ute1)}), tuple_type({ute2, ute3})),
      PrintsAs(u8"('~0 * '~0 list)"));

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

  const auto new_pair_name = type_name(u8"pair", 2, 1);
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
