#include <iostream>
#include <string>
#include "smtparser/frontend/parser.h"
#include <cassert>

int main() {
    std::cout << "======= SMTParser Test Program =======" << std::endl;

    std::cout << "\n--- Testing Boolean Value Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("true");
        assert(result && result->isTrue() && !result->isFalse());
        std::cout << "Input: true" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
        std::cout << "isTrue: yes" << std::endl;
    }
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("false");
        assert(result && result->isFalse() && !result->isTrue());
        std::cout << "Input: false" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
        std::cout << "isFalse: yes" << std::endl;
    }

    std::cout << "\n--- Testing Integer Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("42");
        assert(result && parser->toString(result) == "42");
        std::cout << "Input: 42" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }

    std::cout << "\n--- Testing Real Number Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("3.14");
        assert(result && parser->toString(result) == "3.14");
        std::cout << "Input: 3.14" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }

    std::cout << "\n--- Testing Expression Parsing ---" << std::endl;
    {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr("(and true false)");
        assert(result && result->isFalse());
        std::cout << "Input: (and true false)" << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;
    }

    return 0;
} 