/* -*- Source -*-
 * NL2SMT demo: compile natural language and print assertions + objective
 */
#include "nl2smt/nl2smt.h"
#include "parser.h"
#include <iostream>

int main(int argc, char* argv[]) {
    std::string text = argc > 1 ? argv[1] : "x 是整数 且 x > 0 最小化 x";
    auto parser = SMTParser::newParser();
    SMTParser::NL2SMT::NL2SMTCompiler compiler(parser);
    if (!compiler.compile(text)) {
        std::cerr << "Error: " << compiler.report() << std::endl;
        return 1;
    }
    std::cout << "Assertions:" << std::endl;
    for (const auto& a : parser->getAssertions())
        std::cout << "  " << parser->toString(a) << std::endl;
    std::cout << "Objectives:" << std::endl;
    for (const auto& obj : parser->getObjectives()) {
        if (obj->isMinimize()) std::cout << "  minimize ";
        if (obj->isMaximize()) std::cout << "  maximize ";
        std::cout << parser->toString(obj->getObjectiveTerm()) << std::endl;
    }
    std::cout << "=== SMT2 ===" << std::endl;
    std::cout << parser->dumpSMT2() << std::endl;
    return 0;
}
