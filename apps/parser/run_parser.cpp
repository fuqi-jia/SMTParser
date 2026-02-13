/* -*- Source -*-
 * Parser mode: parse SMT file, output statistics.
 */
#include "parser/run_parser.h"
#include "parser.h"
#include <iostream>

namespace SMTParser {
namespace App {

void printParserUsage(const char* prog) {
    std::cerr << "Usage: " << prog << " parse [options] <file.smt2>\n"
              << "  Parse file with SMTParser and print statistics.\n";
}

int runParser(const char* filePath) {
    if (!filePath || !*filePath) {
        std::cerr << "Error: parse requires a file path.\n";
        return 1;
    }
    auto parser = SMTParser::newParser();
    if (!parser->parse(filePath)) {
        std::cerr << "Parse error: " << filePath << std::endl;
        return 1;
    }

    std::string logic = parser->getOptions() ? parser->getOptions()->getLogic() : "UNKNOWN";
    auto assertions = parser->getAssertions();
    auto variables = parser->getVariables();
    auto functions = parser->getFunctions();
    auto objectives = parser->getObjectives();
    auto softAssertions = parser->getSoftAssertions();
    size_t nodeCount = parser->getNodeCount();

    std::cout << "logic          " << logic << "\n";
    std::cout << "assertions     " << assertions.size() << "\n";
    std::cout << "variables      " << variables.size() << "\n";
    std::cout << "functions      " << functions.size() << "\n";
    std::cout << "objectives     " << objectives.size() << "\n";
    std::cout << "soft_assertions " << softAssertions.size() << "\n";
    std::cout << "nodes          " << nodeCount << "\n";

    return 0;
}

}  // namespace App
}  // namespace SMTParser
