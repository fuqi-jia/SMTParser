#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test combination of arithmetic and boolean logic
void test_arithmetic_boolean_combination(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Arithmetic in boolean context
        "(and (> x 0) (< y 10))",
        
        // Boolean operators with arithmetic comparisons
        "(or (= x y) (and (> x 0) (< y 0)))",
        
        // Implication with arithmetic
        "(=> (>= x 0) (>= (+ x y) y))",
        
        // Ite mixing boolean and arithmetic
        "(ite (> x 0) (+ x y) (- x y))",
        
        // Complex expression mixing theories
        "(and (= (+ x y) z) (or (> x 0) (< y 0)))"
    };
    
    std::cout << "=== Testing Arithmetic and Boolean Logic Combination ===" << std::endl;
    
    try {
        // Declare variables
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during variable declaration: " << e.what() << std::endl;
    }
}

// Test combination of arrays and arithmetic
void test_array_arithmetic_combination(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Array access with arithmetic indices
        "(select a (+ i 1))",
        
        // Store with arithmetic expressions
        "(store a (* 2 i) (+ j 5))",
        
        // Array equality with stores and arithmetic
        "(= (store a i (+ j 1)) (store a i (+ 1 j)))",
        
        // Arrays in arithmetic context
        "(> (select a i) (select a j))",
        
        // Arithmetic constraints on array elements
        "(forall ((k Int)) (=> (and (>= k 0) (< k 10)) (>= (select a k) 0)))"
    };
    
    std::cout << "=== Testing Array and Arithmetic Combination ===" << std::endl;
    
    try {
        // Declare variables and array
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::SortManager::INT_SORT;
        parser->mkArray("a", int_sort, int_sort);
        parser->mkVarInt("i");
        parser->mkVarInt("j");
        parser->mkVarInt("k");
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

// Test combination of bitvectors with other theories
void test_bitvector_combination(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Bitvector in boolean context
        "(= #b1010 #b1010)",
        
        // Bitvector operations with boolean results
        "(bvult #b1010 #b1100)",
        
        // Bitvector with arithmetic
        "(= (bv2nat #b1010) 10)",
        
        // Bitvector in arrays
        "(select a #b1010)",
        
        // Complex bitvector with other theories
        "(and (bvult x y) (= (select a x) #b0101))"
    };
    
    std::cout << "=== Testing Bitvector Combination ===" << std::endl;
    
    try {
        // Declare variables
        std::shared_ptr<SMTParser::Sort> bv4_sort = parser->mkBVSort(4);
        parser->mkVarBv("x", 4);
        parser->mkVarBv("y", 4);
        
        // Declare array from BV to BV
        parser->mkArray("a", bv4_sort, bv4_sort);
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

// Test combination of strings with other theories
void test_string_combination(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // String in boolean context
        "(= \"hello\" \"world\")",
        
        // String with arithmetic
        "(= (str.len s) 5)",
        
        // String indexing with arithmetic
        "(= (str.at s i) \"a\")",
        
        // String in arrays
        "(select a \"key\")",
        
        // Complex string operations with other theories
        "(and (str.prefixof \"pre\" s) (> (str.indexof s \"x\" 0) (+ i j)))"
    };
    
    std::cout << "=== Testing String Combination ===" << std::endl;
    
    try {
        // Declare variables
        std::shared_ptr<SMTParser::Sort> str_sort = SMTParser::SortManager::STR_SORT;
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::SortManager::INT_SORT;
        
        parser->mkVarStr("s");
        parser->mkVarInt("i");
        parser->mkVarInt("j");
        
        // Declare array from string to int
        parser->mkArray("a", str_sort, int_sort);
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

// Test quantifiers with different theories
void test_quantifier_combinations(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Quantifiers with arrays
        "(forall ((i Int)) (=> (and (>= i 0) (< i 10)) (= (select a i) 0)))",
        
        // Quantifiers with bitvectors
        "(exists ((x (_ BitVec 4))) (= (bvadd x #b0001) y))",
        
        // Quantifiers with strings
        "(forall ((c String)) (=> (= (str.len c) 1) (str.contains s c)))",
        
        // Nested quantifiers with mixed theories
        "(forall ((i Int)) (exists ((j Int)) (and (< i j) (= (select a i) (select a j)))))",
        
        // Complex quantifier with multiple theories
        "(exists ((x Int) (y Int)) (and (> x 0) (< y 10) (= (select a x) (select a y))))"
    };
    
    std::cout << "=== Testing Quantifiers with Different Theories ===" << std::endl;
    
    try {
        // Declare variables
        std::shared_ptr<SMTParser::Sort> int_sort = parser->mkIntSort();
        std::shared_ptr<SMTParser::Sort> bv4_sort = parser->mkBVSort(4);
        std::shared_ptr<SMTParser::Sort> str_sort = parser->mkStrSort();
        
        parser->mkArray("a", int_sort, int_sort);
        parser->mkVarBv("y", 4);
        parser->mkVarStr("s");
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

// Test real-world combined theory examples
void test_real_world_examples(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Simple symbolic execution constraint
        "(and (= x (+ y 5)) (= z (* 2 x)) (> z 20))",
        
        // Array bounds checking
        "(=> (and (>= i 0) (< i (array-length a))) (>= (select a i) 0))",
        
        // String password validation
        "(and (>= (str.len password) 8) (str.contains password \"A\") (not (= password \"password\")))",
        
        // Bitvector cryptographic constraint
        "(= (bvxor (bvand x y) (bvor x y)) expected)",
        
        // Combined array and arithmetic optimization
        "(assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (<= (select a i) max_val))))"
    };
    
    std::cout << "=== Testing Real-World Combined Theory Examples ===" << std::endl;
    
    try {
        // Declare variables
        std::shared_ptr<SMTParser::Sort> int_sort = parser->mkIntSort();
        std::shared_ptr<SMTParser::Sort> bv32_sort = parser->mkBVSort(32);
        std::shared_ptr<SMTParser::Sort> str_sort = parser->mkStrSort();
        
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        parser->mkVarInt("i");
        parser->mkVarInt("n");
        parser->mkVarInt("max_val");
        parser->mkVarInt("array-length");
        parser->mkArray("a", int_sort, int_sort);
        parser->mkVarStr("password");
        parser->mkVarBv("x", 32);
        parser->mkVarBv("y", 32);
        parser->mkVarBv("expected", 32);
        
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
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

int main() {
    std::cout << "======= Theory Combination Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_arithmetic_boolean_combination(parser);
    test_array_arithmetic_combination(parser);
    test_bitvector_combination(parser);
    test_string_combination(parser);
    test_quantifier_combinations(parser);
    test_real_world_examples(parser);
    
    return 0;
} 