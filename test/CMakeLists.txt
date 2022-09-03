option(EMIL_ACCEPTANCE_TESTS "Enable acceptance tests for Emil compiler" ON)

if (EMIL_ACCEPTANCE_TESTS)
  add_subdirectory(acceptance)
endif()
