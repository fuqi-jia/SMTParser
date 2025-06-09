#include <iostream>
#include <string>
#include "../include/parser.h"

int main() {
    std::cout << "======= SMTLIBParser Test Program =======" << std::endl;
    
    // Test boolean value parsing
    std::cout << "\n--- Testing Boolean Value Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("true");
        std::cout << "Input: true" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
        std::cout << "isTrue: " << (result->isTrue() ? "yes" : "no") << std::endl;
    }
    
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("false");
        std::cout << "Input: false" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
        std::cout << "isFalse: " << (result->isFalse() ? "yes" : "no") << std::endl;
    }
    
    // Test integer parsing
    std::cout << "\n--- Testing Integer Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("42");
        std::cout << "Input: 42" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }
    
    // Test real number parsing
    std::cout << "\n--- Testing Real Number Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("3.14");
        std::cout << "Input: 3.14" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }
    
    // Test expression parsing
    std::cout << "\n--- Testing Expression Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("(and true false)");
        std::cout << "Input: (and true false)" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }
    
    return 0;
} 