find_package(ICU COMPONENTS uc i18n data REQUIRED)
find_package(fmt REQUIRED)

add_subdirectory("${PROJECT_SOURCE_DIR}/extern/utfcpp" "extern/utfcpp")

add_library(lexer STATIC lexer.cc source.cc)
add_emil_options(lexer)

target_include_directories(lexer PUBLIC ../include)
target_link_libraries(lexer PUBLIC fmt::fmt utf8cpp ICU::uc ICU::data)
