/* -*- C++ -*-
 *
 * Test for GlobalOptions toString() method
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 */

#include "parser.h"
#include <iostream>

using namespace SMTParser;

int main() {
    // Create a new parser
    auto parser = newParser();
    
    std::cout << "=== Test 1: Default Configuration ===" << std::endl;
    std::cout << parser->optionToString() << std::endl;
    
    std::cout << "\n\n=== Test 2: Modified Configuration ===" << std::endl;
    
    // Modify some options via getOptions()
    parser->getOptions()->setLogic("QF_LIA");
    parser->getOptions()->setEvaluatePrecision(256);
    parser->getOptions()->setKeepLet(false);
    parser->getOptions()->setKeepDivision(false);
    parser->getOptions()->setEvaluateUseFloating(false);
    parser->getOptions()->setExpandRecursiveFunctions(true);
    
    std::cout << parser->optionToString() << std::endl;
    
    std::cout << "\n\n=== Test 3: Using setOption method ===" << std::endl;
    
    // Create another parser and set options via string interface
    auto parser2 = newParser();
    parser2->getOptions()->setOption("keep_let", "false");
    parser2->getOptions()->setOption("precision", "512");
    parser2->getOptions()->setOption("float_evaluate", "false");
    parser2->getOptions()->setOption("keep_division", "false");
    parser2->getOptions()->setOption("expand_recursive_functions", "true");
    parser2->getOptions()->setLogic("QF_BV");
    
    std::cout << parser2->optionToString() << std::endl;
    
    std::cout << "\n\n=== Test 4: Parsing file with options ===" << std::endl;
    
    // Parse a simple SMT-LIB2 content with set-info and set-option
    auto parser3 = newParser();
    parser3->parseStr("(set-logic QF_UFLIA)");
    parser3->parseStr("(set-info :source \"Test source\")");
    parser3->parseStr("(set-info :smt-lib-version \"2.6\")");
    parser3->parseStr("(set-option :produce-models true)");
    parser3->parseStr("(declare-const x Int)");
    parser3->parseStr("(assert (> x 0))");
    parser3->parseStr("(check-sat)");
    
    std::cout << parser3->optionToString() << std::endl;
    
    return 0;
}

