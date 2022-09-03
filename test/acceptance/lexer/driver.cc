#include <fmt/core.h>

#include <fstream>
#include <iostream>
#include <iterator>
#include <string>

#include "emil/lexer.h"
#include "emil/source.h"
#include "emil/token.h"
#include "utf8/cpp17.h"

namespace emil {
namespace testing {

bool process_next_token(Lexer& lexer, std::ostreambuf_iterator<char>& out) {
  try {
    auto token = lexer.next_token();
    fmt::format_to(out, "{}\n", token);
    return token.type != TokenType::END;
  } catch (LexingError& err) {
    std::cerr << err.full_msg << "\n"
              << utf8::utf32to8(err.partial_token_text) << "\n";
    fmt::format_to(out, "{:04} ERROR\n", err.line);
    lexer.advance_past(U"(*xx*)");
    return true;
  }
}

}  // namespace testing
}  // namespace emil

int main(int argc, char** argv) {
  if (argc != 3) {
    fmt::print(stderr, "Usage: {} INFILE OUTFILE", argv[0]);
    return 1;
  }

  const std::string infile(argv[1]);
  std::basic_ifstream<char32_t> stream(infile);
  emil::Lexer lexer(infile, emil::make_source(stream));

  const std::string outfile(argv[2]);
  std::ofstream outstream(outfile);
  std::ostreambuf_iterator<char> out(outstream);

  while (emil::testing::process_next_token(lexer, out)) {
  }
}
