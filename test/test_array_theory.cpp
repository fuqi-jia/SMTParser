#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test array creation and basic operations
void test_array_creation(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Array Creation ===" << std::endl;
    
    try {
        // Create an array from Int to Int
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::SortManager::INT_SORT;
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

int main() {
    std::cout << "======= Array Theory Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_array_creation(parser);
    test_array_operations(parser);
    
    return 0;
} 