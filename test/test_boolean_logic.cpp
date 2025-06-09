#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test basic boolean constants
void test_boolean_constants(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "true",
        "false"
    };
    
    std::cout << "=== Testing Boolean Constants ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
            std::cout << "  isTrue: " << (result->isTrue() ? "yes" : "no") << std::endl;
            std::cout << "  isFalse: " << (result->isFalse() ? "yes" : "no") << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// Test logical operations
void test_logical_operations(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(not true)",
        "(not false)",
        "(and true true)",
        "(and true false)",
        "(and false false)",
        "(or true true)",
        "(or true false)",
        "(or false false)",
        "(=> true true)",
        "(=> true false)",
        "(=> false true)",
        "(=> false false)",
        "(xor true true)",
        "(xor true false)",
        "(xor false false)"
    };
    
    std::cout << "=== Testing Logical Operations ===" << std::endl;
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

// Test complex boolean expressions
void test_complex_expressions(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(and (or true false) (not false))",
        "(or (and true false) (not true))",
        "(=> (or true false) (and true true))",
        "(xor (not false) (and true false))",
        "(and (=> true false) (or false true))",
        "(not (and (or true false) (=> false true)))"
    };
    
    std::cout << "=== Testing Complex Boolean Expressions ===" << std::endl;
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
    std::cout << "======= Boolean Logic Operations Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_boolean_constants(parser);
    test_logical_operations(parser);
    test_complex_expressions(parser);
    
    return 0;
} 