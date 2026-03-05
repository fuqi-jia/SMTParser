#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"
#include <cassert>

// Test array creation and basic operations
void test_array_creation(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Array Creation ===" << std::endl;
    
    std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::SortManager::INT_SORT;
    std::shared_ptr<SMTParser::DAGNode> array = parser->mkArray("testArray", int_sort, int_sort);
    assert(array);
    assert(parser->toString(array).find("testArray") != std::string::npos);
    std::cout << "Created array: " << parser->toString(array) << std::endl;
    std::cout << std::endl;
}

// Test array store and select operations
void test_array_operations(SMTParser::ParserPtr& parser) {
    std::vector<std::pair<std::string, std::string>> cases = {
        {"((as const (Array Int Int)) 0)", "0"},
        {"(store ((as const (Array Int Int)) 0) 1 10)", ""},
        {"(select (store ((as const (Array Int Int)) 0) 1 10) 1)", "10"},
        {"(select (store ((as const (Array Int Int)) 0) 1 10) 2)", "0"},
        {"(= (select (store ((as const (Array Int Int)) 0) 1 10) 1) 10)", "true"},
        {"(store (store ((as const (Array Int Int)) 0) 1 10) 2 20)", ""}
    };
    
    std::cout << "=== Testing Array Operations ===" << std::endl;
    for (const auto& p : cases) {
        std::cout << "Expression: " << p.first << std::endl;
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(p.first);
        assert(result);
        std::string got = parser->toString(result);
        std::cout << "  Result: " << got << std::endl;
        if (!p.second.empty()) {
            assert(got == p.second && "array operation result mismatch");
        } else {
            assert(got.find("store") != std::string::npos || got.find("select") != std::string::npos || got.find("const") != std::string::npos);
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