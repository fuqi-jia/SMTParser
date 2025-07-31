#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test strings of different lengths
void test_string_lengths(SMTParser::ParserPtr& parser) {
    std::vector<std::string> test_strings = {
        "", // Empty string
        "true",
        "false",
        "a_very_long_identifier_name_to_test_buffer_handling",
        "(and (or true false) (not true))",
        std::string(1000, 'a') // String of 1000 'a' characters
    };
    
    for (const auto& str : test_strings) {
        std::cout << "Testing string length: " << str.length() << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkConstStr(str);
            std::cout << "  Result: " << (result->isErr() ? "Error" : parser->toString(result)) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
    }
}

// Test special characters
void test_special_chars(SMTParser::ParserPtr& parser) {
    std::vector<std::string> test_strings = {
        "\"quoted string\"",
        // "|symbol with spaces|", -> error
        // ";comment", -> error
        "(and (or true false) (not true))"
    };
    
    for (const auto& str : test_strings) {
        std::cout << "Testing special character: " << str << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(str);
            std::cout << "  Result: " << (result->isErr() ? "Error" : parser->toString(result)) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
    }
}

int main() {
    std::cout << "======= String Handling Safety Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    std::cout << "\n--- Testing String Lengths ---" << std::endl;
    test_string_lengths(parser);
    
    std::cout << "\n--- Testing Special Characters ---" << std::endl;
    test_special_chars(parser);
    
    return 0;
} 