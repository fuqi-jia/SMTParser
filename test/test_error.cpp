#include <iostream>
#include <string>
#include <vector>
#include <cstdio>
#include "../include/parser.h"

// Test function to check file existence
bool file_exists(const std::string& filename) {
    FILE* file = fopen(filename.c_str(), "r");
    if (file) {
        fclose(file);
        return true;
    }
    return false;
}

// Test function to parse a specific SMT2 file and report results
void test_parse_file(const std::string& filename,SMTParser::ParserPtr& parser) {
    std::cout << "\n=== Testing file: " << filename << " ===" << std::endl;
    // Check if file exists
    if (!file_exists(filename)) {
        std::cerr << "Error: Test file not found: " << filename << std::endl;
        std::cerr << "Please make sure the file exists in the correct location." << std::endl;
        return ;
    }

    // Set parser options
    parser->setOption("keep_let", false);
    parser->setOption("preserve_let", false);
    
    // Parse the file
    bool parse_success = parser->parse(filename);
    
    // Report results
    if (parse_success) {
        std::cout << "✓ PARSE_SUCCESS" << std::endl;
        
        // Get statistics
        auto assertions = parser->getAssertions();
        auto variables = parser->getVariables();
        auto functions = parser->getFunctions();
        auto nodes = parser->getNodeCount();
        
        std::cout << "  Assertions: " << assertions.size() << std::endl;
        std::cout << "  Variables: " << variables.size() << std::endl;
        std::cout << "  Functions: " << functions.size() << std::endl;
        std::cout << "  Total Nodes: " << nodes << std::endl;
        
        // Print some details about the parsed content
        std::cout << "\n  --- Parsed Content Details ---" << std::endl;
        
        // Print variables
        if (!variables.empty()) {
            std::cout << "  Variables:" << std::endl;
            for (const auto& var : variables) {
                std::cout << "    " << var->getName() << " : " << parser->toString(var->getSort()) << std::endl;
            }
        }
        
        // Print functions
        if (!functions.empty()) {
            std::cout << "  Functions:" << std::endl;
            for (const auto& func : functions) {
                std::cout << "    " << func->getName() << std::endl;
            }
        }
        
        // Print first few assertions
        if (!assertions.empty()) {
            std::cout << "  Assertions (first 3):" << std::endl;
            for (size_t i = 0; i < std::min(assertions.size(), size_t(3)); ++i) {
                std::cout << "    " << (i+1) << ". " << parser->toString(assertions[i]) << std::endl;
            }
            if (assertions.size() > 3) {
                std::cout << "    ... and " << (assertions.size() - 3) << " more assertions" << std::endl;
            }
        }
        
    } else {
        std::cout << "✗ PARSE_FAILURE" << std::endl;
    }
}


int main() {
    std::cout << "======= Parser Error Test =======" << std::endl;

    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    // Test 1: Parse the file with kind mismatch
    test_parse_file("../test/instances/error_kind_mismatch.smt2",parser);
    //已解决，问题在于op_parser.cpp中Parser::mkSub的getSort()，该方法没有考虑isIntOrReal

    parser = SMTParser::newParser();
    // Test 2: Parse the file with unknown symbol
    test_parse_file("../test/instances/error_unknown_symbol.smt2",parser);
    //已定位问题，未添加keyword [:named]，且该keyword需要特别的语法支持(! <formula> :named <name>)

    parser = SMTParser::newParser();
    // Test 3: Parse the file with unknown symbol
    test_parse_file("../test/instances/error_unknown_symbol_2.smt2",parser);

    std::cout << "\n======= Test Complete =======" << std::endl;
    
    return 0;
} 