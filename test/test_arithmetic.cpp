#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test integer arithmetic operations
void test_integer_arithmetic(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "42",
        "-15",
        "(+ 10 20)",
        "(- 50 30)",
        "(* 6 7)",
        "(div 20 5)",
        "(mod 17 5)",
        "(abs -42)"
    };
    
    std::cout << "=== Testing Integer Arithmetic ===" << std::endl;
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

// Test real number arithmetic operations
void test_real_arithmetic(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "3.14159",
        "-2.71828",
        "(+ 3.5 2.7)",
        "(- 10.5 4.2)",
        "(* 2.5 4.0)",
        "(/ 15.0 3.0)",
        "(^ 2.0 3.0)",      // 2.0^3.0
        "(sqrt 16.0)",
        "(abs -9.81)"
    };
    
    std::cout << "=== Testing Real Number Arithmetic ===" << std::endl;
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

// Test arithmetic comparison operations
void test_comparisons(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(< 5 10)",
        "(<= 7 7)",
        "(> 15 5)",
        "(>= 12 12)",
        "(= 42 42)",
        "(distinct 3 5 7)"
    };
    
    std::cout << "=== Testing Arithmetic Comparisons ===" << std::endl;
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

void test_precision(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Precision ===" << std::endl;
    
    // Default precision (128 bits)
    std::cout << "=== Default Precision (128 bits) ===" << std::endl;
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(+ 3.5 2.7)")) << std::endl;
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(- 10.5 4.2)")) << std::endl;
    
    // Set higher precision (256 bits)
    parser->setEvaluatePrecision(256);
    std::cout << "\n=== Higher Precision (256 bits) ===" << std::endl;
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(+ 3.5 2.7)")) << std::endl;
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(- 10.5 4.2)")) << std::endl;
    
    // Disable floating point mode
    parser->setEvaluateUseFloating(false);
    std::cout << "\n=== Disable Floating Point Mode ===" << std::endl;
    std::cout << "Expression: (+ 3.5 2.7)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(+ 3.5 2.7)")) << std::endl;
    std::cout << "Expression: (- 10.5 4.2)" << std::endl;
    std::cout << "  Result: " << parser->toString(parser->mkExpr("(- 10.5 4.2)")) << std::endl;
}

int main() {
    std::cout << "======= Arithmetic Operations Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_integer_arithmetic(parser);
    test_real_arithmetic(parser);
    test_comparisons(parser);
    test_precision(parser);
    
    return 0;
} 