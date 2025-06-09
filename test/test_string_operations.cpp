#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test string constants
void test_string_constants(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "\"\"",                       // Empty string
        "\"Hello, World!\"",          // Simple string
        "\"String with \\\"quotes\\\"\"", // String with escaped quotes
        "\"String with \\\\backslash\"",  // String with escaped backslash
        "\"Multi-line\nstring\""      // Multi-line string
    };
    
    std::cout << "=== Testing String Constants ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// Test string operations
void test_string_operations(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(str.len \"Hello\")",
        "(str.++ \"Hello, \" \"World!\")",
        "(str.at \"Hello\" 1)",
        "(str.substr \"Hello, World!\" 7 5)",
        "(str.indexof \"Hello, World!\" \"World\" 0)",
        "(str.replace \"Hello, World!\" \"World\" \"Universe\")",
        "(str.prefixof \"Hello\" \"Hello, World!\")",
        "(str.suffixof \"World!\" \"Hello, World!\")",
        "(str.contains \"Hello, World!\" \"World\")"
    };
    
    std::cout << "=== Testing String Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// Test string comparison operations
void test_string_comparisons(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(= \"Hello\" \"Hello\")",
        "(= \"Hello\" \"World\")",
        "(str.< \"Hello\" \"World\")",
        "(str.<= \"Hello\" \"Hello\")",
        "(str.> \"World\" \"Hello\")",
        "(str.>= \"World\" \"World\")"
    };
    
    std::cout << "=== Testing String Comparison Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// Test regular expression operations
void test_regex_operations(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(str.in_re \"abc\" (re.* (re.range \"a\" \"z\")))",
        "(str.in_re \"123\" (re.+ (re.range \"0\" \"9\")))",
        "(str.in_re \"abc\" (re.union (re.* (re.range \"a\" \"z\")) (re.* (re.range \"0\" \"9\"))))",
        "(str.in_re \"\" re.allchar)",
        "(str.in_re \"abc\" (re.++ (re.range \"a\" \"a\") (re.range \"b\" \"b\") (re.range \"c\" \"c\")))"
    };
    
    std::cout << "=== Testing Regular Expression Operations ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

int main() {
    std::cout << "======= String Operations Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_string_constants(parser);
    test_string_operations(parser);
    test_string_comparisons(parser);
    test_regex_operations(parser);
    
    return 0;
} 