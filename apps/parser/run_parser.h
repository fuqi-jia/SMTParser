/* -*- Header -*-
 * Parser mode: parse SMT file with SMTParser, output statistics.
 */
#ifndef APPS_PARSER_RUN_PARSER_HEADER
#define APPS_PARSER_RUN_PARSER_HEADER

namespace SMTParser {
namespace App {

/** Parse file with SMTParser and print stats to stdout. Return 0 on success. */
int runParser(const char* filePath);

void printParserUsage(const char* prog);

}  // namespace App
}  // namespace SMTParser

#endif
