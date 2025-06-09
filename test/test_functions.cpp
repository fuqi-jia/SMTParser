#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test basic function declarations
void test_function_declarations(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Function Declarations ===" << std::endl;
    
    try {
        // Create sorts
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::INT_SORT;
        std::shared_ptr<SMTParser::Sort> bool_sort = SMTParser::BOOL_SORT;
        std::shared_ptr<SMTParser::Sort> real_sort = SMTParser::REAL_SORT;
        
        // Declare a function with no arguments (constant)
        std::vector<std::shared_ptr<SMTParser::Sort>> const_params;
        std::shared_ptr<SMTParser::DAGNode> const_func = parser->mkFuncDec("c", const_params, int_sort);
        std::cout << "Constant function: " << parser->toString(const_func) << std::endl;
        
        // Declare a unary function
        std::vector<std::shared_ptr<SMTParser::Sort>> unary_params = {int_sort};
        std::shared_ptr<SMTParser::DAGNode> unary_func = parser->mkFuncDec("f", unary_params, int_sort);
        std::cout << "Unary function: " << parser->toString(unary_func) << std::endl;
        
        // Declare a binary function
        std::vector<std::shared_ptr<SMTParser::Sort>> binary_params = {int_sort, int_sort};
        std::shared_ptr<SMTParser::DAGNode> binary_func = parser->mkFuncDec("g", binary_params, int_sort);
        std::cout << "Binary function: " << parser->toString(binary_func) << std::endl;
        
        // Declare a predicate function
        std::vector<std::shared_ptr<SMTParser::Sort>> pred_params = {int_sort, int_sort};
        std::shared_ptr<SMTParser::DAGNode> pred_func = parser->mkFuncDec("p", pred_params, bool_sort);
        std::cout << "Predicate function: " << parser->toString(pred_func) << std::endl;
        
        // Declare a function with mixed argument types
        std::vector<std::shared_ptr<SMTParser::Sort>> mixed_params = {int_sort, real_sort, bool_sort};
        std::shared_ptr<SMTParser::DAGNode> mixed_func = parser->mkFuncDec("h", mixed_params, real_sort);
        std::cout << "Mixed function: " << parser->toString(mixed_func) << std::endl;
    } catch (const std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
    }
    
    std::cout << std::endl;
}

// Test basic function definitions and applications
void test_function_definitions(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Function definition using define-fun
        "(define-fun inc ((x Int)) Int (+ x 1))",
        
        // Function application
        "(inc 5)",
        
        // More complex function definition
        "(define-fun max2 ((x Int) (y Int)) Int (ite (>= x y) x y))",
        
        // Application of max2
        "(max2 10 20)",
        
        // Recursive function definition using define-fun-rec
        "(define-fun-rec factorial ((n Int)) Int (ite (<= n 1) 1 (* n (factorial (- n 1)))))",
        
        // Application of factorial
        "(factorial 5)",
        
        // Mutually recursive functions using define-funs-rec
        "(define-funs-rec ((is-even ((n Int)) Bool) (is-odd ((n Int)) Bool)) ((ite (= n 0) true (is-odd (- n 1))) (ite (= n 0) false (is-even (- n 1)))))",
        
        // Application of mutually recursive functions
        "(is-even 4)",
        "(is-odd 3)"
    };
    
    std::cout << "=== Testing Function Definitions ===" << std::endl;
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

// Test manual function definition and application
void test_manual_function_definition(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Manual Function Definition ===" << std::endl;
    
    try {
        // Create sorts
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::INT_SORT;
        
        // Create function parameter
        std::shared_ptr<SMTParser::DAGNode> x_param = parser->mkFunParamVar(int_sort, "x");
        std::vector<std::shared_ptr<SMTParser::DAGNode>> params = {x_param};
        
        // Create function body: x + 1
        std::shared_ptr<SMTParser::DAGNode> one = parser->mkConstInt(1);
        std::shared_ptr<SMTParser::DAGNode> body = parser->mkAdd(x_param, one);
        
        // Create function definition: inc(x) = x + 1
        std::shared_ptr<SMTParser::DAGNode> inc_func = parser->mkFuncDef("inc_manual", params, int_sort, body);
        std::cout << "Manually defined function: " << parser->toString(inc_func) << std::endl;
        
        // Create function application: inc(5)
        std::shared_ptr<SMTParser::DAGNode> five = parser->mkConstInt(5);
        std::vector<std::shared_ptr<SMTParser::DAGNode>> app_params = {five};
        std::shared_ptr<SMTParser::DAGNode> app = parser->mkApplyFunc(inc_func, app_params);
        std::cout << "Function application: " << parser->toString(app) << std::endl;
        
    } catch (const std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
    }
    
    std::cout << std::endl;
}

// Test higher-order functions and complex function applications
void test_complex_functions(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Define compose function: compose(f, g, x) = f(g(x))
        "(define-fun compose ((f (-> Int Int)) (g (-> Int Int)) (x Int)) Int (f (g x)))",
        
        // Define increment function
        "(define-fun inc ((x Int)) Int (+ x 1))",
        
        // Define double function
        "(define-fun double ((x Int)) Int (* x 2))",
        
        // Apply compose: compose(inc, double, 3) = inc(double(3)) = inc(6) = 7
        "(compose inc double 3)",
        
        // Apply compose in reverse: compose(double, inc, 3) = double(inc(3)) = double(4) = 8
        "(compose double inc 3)",
        
        // Define a higher-order function that returns a function
        "(define-fun make-adder ((n Int)) (-> Int Int) (lambda ((x Int)) (+ x n)))",
        
        // Apply the returned function
        "((make-adder 5) 3)",
        
        // Define a curried function
        "(define-fun curry-add ((x Int)) (-> Int Int) (lambda ((y Int)) (+ x y)))",
        
        // Apply the curried function
        "((curry-add 2) 3)"
    };
    
    std::cout << "=== Testing Complex Functions ===" << std::endl;
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

// Test function assertions and constraints
void test_function_constraints(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Declare function f: Int -> Int
        "(declare-fun f (Int) Int)",
        
        // Assert properties about f
        "(assert (= (f 0) 0))",
        "(assert (= (f 1) 1))",
        
        // Assert that f is increasing
        "(assert (forall ((x Int) (y Int)) (=> (< x y) (< (f x) (f y)))))",
        
        // Define function g: Int -> Int such that g(x) = 2*x
        "(define-fun g ((x Int)) Int (* 2 x))",
        
        // Assert that f and g commute for some value
        "(assert (exists ((x Int)) (= (f (g x)) (g (f x)))))",
        
        // Check satisfiability
        "(check-sat)"
    };
    
    std::cout << "=== Testing Function Constraints ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            if (expr.find("declare-fun") != std::string::npos || expr.find("define-fun") != std::string::npos) {
                std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
                std::cout << "  Declared/Defined: " << parser->toString(result) << std::endl;
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
    std::cout << "======= Functions Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_function_declarations(parser);
    test_function_definitions(parser);
    test_manual_function_definition(parser);
    test_complex_functions(parser);
    test_function_constraints(parser);
    
    return 0;
} 