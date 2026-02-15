/* -*- Source -*-
 * Feature subcommand: parse SMT file and print syntax features.
 */
#include "features/run_features.h"
#include "parser.h"
#include <iostream>
#include <cstdlib>

namespace SMTParser {
namespace App {

int runFeatures(const char* smtFilePath) {
    if (!smtFilePath || !smtFilePath[0]) {
        std::cerr << "Error: feature requires <file.smt2>.\n";
        return 1;
    }
    auto parser = SMTParser::newParser();
    if (!parser->parse(smtFilePath)) {
        std::cerr << "Parse error: " << smtFilePath << std::endl;
        return 1;
    }
    std::string logic = parser->getOptions() ? parser->getOptions()->getLogic() : "UNKNOWN_LOGIC";
    auto assertions = parser->getAssertions();
    auto objectives = parser->getObjectives();
    auto variables = parser->getVariables();
    auto functions = parser->getFunctions();
    std::cout << "logic " << logic << std::endl;
    std::cout << "assertions " << assertions.size() << std::endl;
    std::cout << "objectives " << objectives.size() << std::endl;
    std::cout << "variables " << variables.size() << std::endl;
    std::cout << "functions " << functions.size() << std::endl;
    return 0;
}

}  // namespace App
}  // namespace SMTParser
