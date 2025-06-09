#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test array creation and basic operations
void test_array_creation(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Array Creation ===" << std::endl;
    
    try {
        // Create an array from Int to Int
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::INT_SORT;
        std::shared_ptr<SMTParser::DAGNode> array = parser->mkArray("testArray", int_sort, int_sort);
        std::cout << "Created array: " << parser->toString(array) << std::endl;
    } catch (const std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
    }
    
    std::cout << std::endl;
}

// Test array store and select operations
void test_array_operations(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "((as const (Array Int Int)) 0)",                       // Constant array filled with 0
        "(store ((as const (Array Int Int)) 0) 1 10)",          // Store 10 at index 1
        "(select (store ((as const (Array Int Int)) 0) 1 10) 1)", // Select index 1 (should be 10)
        "(select (store ((as const (Array Int Int)) 0) 1 10) 2)", // Select index 2 (should be 0)
        "(= (select (store ((as const (Array Int Int)) 0) 1 10) 1) 10)", // Equality check
        "(store (store ((as const (Array Int Int)) 0) 1 10) 2 20)"  // Multiple stores
    };
    
    std::cout << "=== Testing Array Operations ===" << std::endl;
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

// Test array assertions and constraints
void test_array_constraints(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(declare-const a (Array Int Int))",
        "(declare-const b (Array Int Int))",
        "(assert (= (select a 1) 10))",
        "(assert (= (select a 2) 20))",
        "(assert (= b (store a 3 30)))",
        "(assert (= (select b 3) 30))",
        "(assert (= (select b 1) (select a 1)))",
        "(check-sat)"
    };
    
    std::cout << "=== Testing Array Constraints ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            if (expr.find("declare-const") != std::string::npos) {
                // Extract name and sort
                size_t name_start = expr.find(' ') + 1;
                size_t name_end = expr.find(' ', name_start);
                std::string name = expr.substr(name_start, name_end - name_start);
                std::string sort = expr.substr(name_end + 1, expr.find(')') - name_end - 1);
                
                if (sort == "(Array Int Int)") {
                    std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::INT_SORT;
                    std::shared_ptr<SMTParser::DAGNode> array = parser->mkArray(name, int_sort, int_sort);
                    std::cout << "  Declared array: " << parser->toString(array) << std::endl;
                }
            } else if (expr.find("assert") != std::string::npos) {
                std::string assertion = expr.substr(expr.find('(', 1), expr.rfind(')') - expr.find('(', 1) + 1);
                std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(assertion);
                parser->assert(result);
                std::cout << "  Asserted: " << parser->toString(result) << std::endl;
            } else if (expr == "(check-sat)") {
                SMTParser::RESULT_TYPE result = parser->checkSat();
                std::cout << "  Result: ";
                switch (result) {
                    case SMTParser::RESULT_TYPE::RT_SAT: std::cout << "sat"; break;
                    case SMTParser::RESULT_TYPE::RT_UNSAT: std::cout << "unsat"; break;
                    case SMTParser::RESULT_TYPE::RT_UNKNOWN: std::cout << "unknown"; break;
                    default: std::cout << "error"; break;
                }
                std::cout << std::endl;
            } else {
                std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
                std::cout << "  Result: " << parser->toString(result) << std::endl;
            }
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

int main() {
    std::cout << "======= Array Theory Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_array_creation(parser);
    test_array_operations(parser);
    test_array_constraints(parser);
    
    return 0;
} 