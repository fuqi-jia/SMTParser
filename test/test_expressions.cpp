#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// Test let expressions
void test_let_expressions(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Simple let expression
        "(let ((x 10)) (+ x 5))",
        
        // Multiple bindings
        "(let ((x 10) (y 20)) (+ x y))",
        
        // Nested let expressions
        "(let ((x 10)) (let ((y (* 2 x))) (+ x y)))",
        
        // Let with shadowing
        "(let ((x 10)) (let ((x 20)) (+ x 5)))",
        
        // Let with complex expressions
        "(let ((x (+ 1 2)) (y (* 3 4))) (- y x))",
        
        // Let with boolean expressions
        "(let ((x true) (y false)) (and x (not y)))"
    };
    
    std::cout << "=== Testing Let Expressions ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "Expression: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  Result: " << parser->toString(result) << std::endl;
            
            // Expand let expression
            std::shared_ptr<SMTParser::DAGNode> expanded = parser->expandLet(result);
            std::cout << "  Expanded: " << parser->toString(expanded) << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  Exception: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// Test normal forms (NNF, CNF, DNF)
void test_normal_forms(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Simple formula
        "(not (and a b))",
        
        // More complex formula
        "(=> (and a b) (or c d))",
        
        // Formula with nested operations
        "(or (and a b) (and c d))",
        
        // Formula with negations
        "(not (or (not a) (and b (not c))))",
        
        // Formula with implications
        "(=> (=> a b) c)",
        
        // Formula with equivalence
        "(= (and a b) (or c d))"
    };
    
    std::cout << "=== Testing Normal Forms ===" << std::endl;
    
    // First declare boolean variables
    try {
        parser->mkVarBool("a");
        parser->mkVarBool("b");
        parser->mkVarBool("c");
        parser->mkVarBool("d");
        
        for (const auto& expr : expressions) {
            std::cout << "Expression: " << expr << std::endl;
            try {
                std::shared_ptr<SMTParser::DAGNode> original = parser->mkExpr(expr);
                std::cout << "  Original: " << parser->toString(original) << std::endl;
                
                // Convert to NNF
                std::shared_ptr<SMTParser::DAGNode> nnf = parser->toNNF(original);
                std::cout << "  NNF: " << parser->toString(nnf) << std::endl;
                
                // Convert to CNF
                std::vector<std::shared_ptr<SMTParser::DAGNode>> expr_vec = {original};
                std::shared_ptr<SMTParser::DAGNode> cnf = parser->toCNF(expr_vec);
                std::cout << "  CNF: " << parser->toString(cnf) << std::endl;
                
                // Convert to DNF
                std::shared_ptr<SMTParser::DAGNode> dnf = parser->toDNF(original);
                std::cout << "  DNF: " << parser->toString(dnf) << std::endl;
            } catch (const std::exception& e) {
                std::cout << "  Exception: " << e.what() << std::endl;
            }
            std::cout << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "Exception during variable declaration: " << e.what() << std::endl;
    }
}

// Test arithmetic normalization
void test_arithmetic_normalization(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Simple comparison
        "(< (+ x 2) 5)",
        
        // Comparison with variables on both sides
        "(= (+ x 2) (+ y 3))",
        
        // Complex arithmetic expression
        "(>= (+ (* 2 x) (* 3 y)) (* 4 z))",
        
        // Mixed arithmetic and boolean operations
        "(and (> x 0) (< y 10))",
        
        // Nested comparisons
        "(or (< x y) (> x z))"
    };
    
    std::cout << "=== Testing Arithmetic Normalization ===" << std::endl;
    
    // Declare variables
    try {
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        
        for (const auto& expr : expressions) {
            std::cout << "Expression: " << expr << std::endl;
            try {
                std::shared_ptr<SMTParser::DAGNode> original = parser->mkExpr(expr);
                std::cout << "  Original: " << parser->toString(original) << std::endl;
                
                // Normalize
                std::shared_ptr<SMTParser::DAGNode> normalized = parser->arithNormalize(original);
                std::cout << "  Normalized: " << parser->toString(normalized) << std::endl;
            } catch (const std::exception& e) {
                std::cout << "  Exception: " << e.what() << std::endl;
            }
            std::cout << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "Exception during variable declaration: " << e.what() << std::endl;
    }
}

// Test binarization of operations
void test_binarization(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // N-ary and
        "(and a b c d)",
        
        // N-ary or
        "(or a b c d)",
        
        // N-ary equality
        "(= x y z)",
        
        // N-ary addition
        "(+ x y z)",
        
        // N-ary multiplication
        "(* x y z)",
        
        // Mixed operations
        "(and (or a b c) (= x y z))",
        
        // Nested operations
        "(and (or a b) (or c d) (or e f))"
    };
    
    std::cout << "=== Testing Binarization ===" << std::endl;
    
    // Declare variables
    try {
        parser->mkVarBool("a");
        parser->mkVarBool("b");
        parser->mkVarBool("c");
        parser->mkVarBool("d");
        parser->mkVarBool("e");
        parser->mkVarBool("f");
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        
        for (const auto& expr : expressions) {
            std::cout << "Expression: " << expr << std::endl;
            try {
                std::shared_ptr<SMTParser::DAGNode> original = parser->mkExpr(expr);
                std::cout << "  Original: " << parser->toString(original) << std::endl;
                
                // Binarize
                std::shared_ptr<SMTParser::DAGNode> binarized = parser->binarizeOp(original);
                std::cout << "  Binarized: " << parser->toString(binarized) << std::endl;
            } catch (const std::exception& e) {
                std::cout << "  Exception: " << e.what() << std::endl;
            }
            std::cout << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "Exception during variable declaration: " << e.what() << std::endl;
    }
}

// Test collecting atoms and variables
void test_collect_atoms_variables(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        // Mixed boolean and arithmetic
        "(and (> x 0) (< y 10) (= z 5))",
        
        // Complex nested expression
        "(or (and (> x 0) (< y 10)) (not (= z 5)))",
        
        // Expression with functions
        "(and (p x y) (q z))"
    };
    
    std::cout << "=== Testing Collecting Atoms and Variables ===" << std::endl;
    
    // Declare variables and functions
    try {
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        
        std::shared_ptr<SMTParser::Sort> int_sort = SMTParser::INT_SORT;
        std::shared_ptr<SMTParser::Sort> bool_sort = SMTParser::BOOL_SORT;
        
        std::vector<std::shared_ptr<SMTParser::Sort>> p_params = {int_sort, int_sort};
        parser->mkFuncDec("p", p_params, bool_sort);
        
        std::vector<std::shared_ptr<SMTParser::Sort>> q_params = {int_sort};
        parser->mkFuncDec("q", q_params, bool_sort);
        
        for (const auto& expr : expressions) {
            std::cout << "Expression: " << expr << std::endl;
            try {
                std::shared_ptr<SMTParser::DAGNode> formula = parser->mkExpr(expr);
                std::cout << "  Formula: " << parser->toString(formula) << std::endl;
                
                // Collect atoms
                boost::unordered_set<std::shared_ptr<SMTParser::DAGNode>> atoms;
                parser->collectAtoms(formula, atoms);
                
                std::cout << "  Atoms:" << std::endl;
                for (const auto& atom : atoms) {
                    std::cout << "    " << parser->toString(atom) << std::endl;
                }
                
                // Collect variables
                boost::unordered_set<std::shared_ptr<SMTParser::DAGNode>> vars;
                parser->collectVars(formula, vars);
                
                std::cout << "  Variables:" << std::endl;
                for (const auto& var : vars) {
                    std::cout << "    " << parser->toString(var) << std::endl;
                }
            } catch (const std::exception& e) {
                std::cout << "  Exception: " << e.what() << std::endl;
            }
            std::cout << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "Exception during declaration: " << e.what() << std::endl;
    }
}

// Test expression substitution
void test_substitution(SMTParser::ParserPtr& parser) {
    std::cout << "=== Testing Expression Substitution ===" << std::endl;
    
    try {
        // Declare variables
        parser->mkVarInt("x");
        parser->mkVarInt("y");
        parser->mkVarInt("z");
        
        // Create a formula: x + y > z
        std::string expr = "(> (+ x y) z)";
        std::shared_ptr<SMTParser::DAGNode> formula = parser->mkExpr(expr);
        std::cout << "Original formula: " << parser->toString(formula) << std::endl;
        
        // Create substitution map
        boost::unordered_map<std::string, std::shared_ptr<SMTParser::DAGNode>> subst_map;
        subst_map["x"] = parser->mkConstInt(5);
        subst_map["y"] = parser->mkConstInt(10);
        
        // Apply substitution
        std::shared_ptr<SMTParser::DAGNode> substituted = parser->substitute(formula, subst_map);
        std::cout << "After substitution {x->5, y->10}: " << parser->toString(substituted) << std::endl;
        
        // Another substitution
        boost::unordered_map<std::string, std::shared_ptr<SMTParser::DAGNode>> subst_map2;
        subst_map2["z"] = parser->mkConstInt(0);
        
        // Apply another substitution
        std::shared_ptr<SMTParser::DAGNode> substituted2 = parser->substitute(substituted, subst_map2);
        std::cout << "After substitution {z->0}: " << parser->toString(substituted2) << std::endl;
        
        // Create a more complex formula with let
        std::string expr2 = "(let ((a (+ x y))) (> a z))";
        std::shared_ptr<SMTParser::DAGNode> formula2 = parser->mkExpr(expr2);
        std::cout << "Complex formula: " << parser->toString(formula2) << std::endl;
        
        // Apply substitution to complex formula
        std::shared_ptr<SMTParser::DAGNode> substituted3 = parser->substitute(formula2, subst_map);
        std::cout << "After substitution {x->5, y->10}: " << parser->toString(substituted3) << std::endl;
        
    } catch (const std::exception& e) {
        std::cout << "Exception: " << e.what() << std::endl;
    }
    
    std::cout << std::endl;
}

int main() {
    std::cout << "======= Complex Expressions Test =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_let_expressions(parser);
    test_normal_forms(parser);
    test_arithmetic_normalization(parser);
    test_binarization(parser);
    test_collect_atoms_variables(parser);
    test_substitution(parser);
    
    return 0;
} 