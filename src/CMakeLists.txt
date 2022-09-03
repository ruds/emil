find_package(ICU COMPONENTS uc i18n data REQUIRED)

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/fmt" "extern/fmt")
add_subdirectory("${PROJECT_SOURCE_DIR}/extern/utfcpp" "extern/utfcpp")

add_library(lexer STATIC lexer.cc source.cc)

target_include_directories(lexer PUBLIC ../include)
target_link_libraries(lexer PUBLIC fmt utf8cpp ICU::uc ICU::data)

target_compile_features(lexer PUBLIC cxx_std_23)
target_compile_with_warnings(lexer)
