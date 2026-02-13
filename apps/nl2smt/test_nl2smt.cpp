/* -*- Source -*-
 * NL2SMT tests: compile via LLM (mock or real), check assertions and objectives.
 * With mock (default): uses mock_llm.sh so no API key needed.
 */
#include "nl2smt/nl2smt.h"
#include "parser.h"
#include <iostream>
#include <string>
#include <cassert>
#include <cstdlib>

int main() {
#ifdef NL2SMT_MOCK_SCRIPT_PATH
    std::string cmd = "sh ";
    cmd += NL2SMT_MOCK_SCRIPT_PATH;
    setenv("NL2SMT_LLM_CMD", cmd.c_str(), 1);
#else
    if (!getenv("NL2SMT_LLM_SCRIPT") && !getenv("NL2SMT_LLM_CMD")) {
        std::cerr << "Set NL2SMT_LLM_SCRIPT or NL2SMT_LLM_CMD to run test (or build with NL2SMT_MOCK_SCRIPT_PATH)." << std::endl;
        return 0;  // skip, not fail
    }
#endif

    auto parser = SMTParser::newParser();
    SMTParser::NL2SMT::NL2SMTCompiler compiler(parser);

    if (!compiler.compile("x is integer and x > 0, minimize x")) {
        std::cerr << "compile failed: " << compiler.report() << std::endl;
        return 1;
    }
    auto assertions = parser->getAssertions();
    auto objectives = parser->getObjectives();
    assert(assertions.size() >= 1 && "expect at least one assertion from LLM");
    assert(!objectives.empty() && objectives[0]->isMinimize() && "expect minimize objective");
    std::cout << "OK: assertions=" << assertions.size() << " objectives=" << objectives.size() << std::endl;
    std::cout << "All NL2SMT tests passed." << std::endl;
    return 0;
}
