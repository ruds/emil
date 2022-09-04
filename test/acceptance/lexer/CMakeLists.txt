add_executable(driver EXCLUDE_FROM_ALL driver.cc)
target_link_libraries(driver lexer)
target_compile_with_warnings(driver)
add_test(driver_build
  "${CMAKE_COMMAND}"
  --build "${CMAKE_BINARY_DIR}"
  --config $<CONFIG>
  --target driver
)
set_tests_properties(driver_build
  PROPERTIES FIXTURES_SETUP driver_fixture)

macro(lexer_golden_test TESTNAME)
  add_test(
    NAME "${TESTNAME}-create-output"
    COMMAND
    driver "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.in" "${TESTNAME}.out"
  )
  add_test(
    NAME "${TESTNAME}"
    COMMAND
    "${CMAKE_COMMAND}" -E compare_files
    "${TESTNAME}.out"
    "${CMAKE_CURRENT_SOURCE_DIR}/${TESTNAME}.expected"
  )
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_REQUIRED driver_fixture)
  set_tests_properties("${TESTNAME}-create-output"
    PROPERTIES FIXTURES_SETUP "${TESTNAME}_fixture")
  set_tests_properties("${TESTNAME}"
    PROPERTIES FIXTURES_REQUIRED "${TESTNAME}_fixture")
endmacro()

lexer_golden_test(char char.in)
lexer_golden_test(string string.in)
