option(EMIL_ACCEPTANCE_TESTS "Enable acceptance tests for Emil compiler" ON)

if (EMIL_ACCEPTANCE_TESTS)
  add_subdirectory(acceptance)
endif()

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/googletest" "extern/googletest")

mark_as_advanced(
  BUILD_GMOCK BUILD_GTEST BUILD_SHARED_LIBS
  gmock_build_tests gtest_build_samples gtest_build_tests
  gtest_disable_pthreads gtest_force_shared_crt gtest_hide_internal_symbols
)

set_target_properties(gtest PROPERTIES FOLDER extern)
set_target_properties(gtest_main PROPERTIES FOLDER extern)
set_target_properties(gmock PROPERTIES FOLDER extern)
set_target_properties(gmock_main PROPERTIES FOLDER extern)

macro(emil_add_gtest TESTNAME FILES LIBRARIES)
  add_executable(${TESTNAME} "${FILES}")
  add_emil_options(${TESTNAME})
  target_link_libraries(${TESTNAME} gtest gmock gtest_main "${LIBRARIES}")
  gtest_discover_tests(${TESTNAME})
  set_target_properties(${TESTNAME} PROPERTIES FOLDER test)
endmacro()

emil_add_gtest(source_test source_test.cc lexer)
