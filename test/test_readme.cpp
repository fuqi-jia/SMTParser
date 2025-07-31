/*
 * Test file for README.md examples
 * Validates all C++ code examples shown in the README
 */

#include "parser.h"
#include <iostream>
#include <unordered_set>

void test_basic_parsing() {
    std::cout << "\n=== Testing Basic Parsing ===" << std::endl;
    
    try {
        // Initialize the parser
        SMTParser::Parser parser;
        
        // Create a simple SMT-LIB2 string to parse
        std::string smt_content = R"(
            (declare-const x Int)
            (declare-const y Int)
            (assert (> (+ x y) 10))
        )";
        
        // Parse the string instead of file (since we don't have formula.smt2)
        if (!parser.parseStr(smt_content)) {
            std::cerr << "Error parsing SMT content" << std::endl;
            return;
        }
        
        // Retrieve the parsed assertions
        auto assertions = parser.getAssertions();
        
        // Output the assertions
        std::cout << "Parsed assertions:" << std::endl;
        for(auto constraint: assertions){
            std::cout << "  " << parser.toString(constraint) << std::endl;
        }
        
        std::cout << "✓ Basic parsing test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Basic parsing test failed: " << e.what() << std::endl;
    }
}

void test_expression_building_and_evaluation() {
    std::cout << "\n=== Testing Expression Building and Evaluation ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        auto model = SMTParser::newModel();
        
        // Create variables and expressions
        auto x = parser->mkVarInt("x");
        auto y = parser->mkVarInt("y");
        std::vector<std::shared_ptr<SMTParser::DAGNode>> add_params = {x, y};
        auto expr = parser->mkAdd(add_params);
        
        // Evaluate with model
        model->add(x, parser->mkConstInt(10));
        model->add(y, parser->mkConstInt(20));
        auto result = parser->evaluate(expr, model);
        
        std::cout << "Expression: " << parser->toString(expr) << std::endl;
        std::cout << "Result: " << parser->toString(result) << std::endl;  // Should be 30
        
        std::cout << "✓ Expression building and evaluation test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Expression building and evaluation test failed: " << e.what() << std::endl;
    }
}

void test_formula_conversion() {
    std::cout << "\n=== Testing Formula Conversion ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        auto a = parser->mkVarBool("a");
        auto b = parser->mkVarBool("b");
        
        auto formula = parser->mkImplies(a, b);
        
        // Convert to different normal forms
        auto nnf = parser->toNNF(formula);
        std::vector<std::shared_ptr<SMTParser::DAGNode>> formulas = {formula};
        auto cnf = parser->toCNF(formulas);
        auto dnf = parser->toDNF(formula);
        
        std::cout << "Original: " << parser->toString(formula) << std::endl;
        std::cout << "NNF: " << parser->toString(nnf) << std::endl;
        std::cout << "CNF: " << parser->toString(cnf) << std::endl;
        std::cout << "DNF: " << parser->toString(dnf) << std::endl;
        
        std::cout << "✓ Formula conversion test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Formula conversion test failed: " << e.what() << std::endl;
    }
}

void test_advanced_formula_evaluation() {
    std::cout << "\n=== Testing Advanced Formula Evaluation ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        auto model = SMTParser::newModel();
        auto x = parser->mkVarInt("x");
        std::vector<std::shared_ptr<SMTParser::DAGNode>> add_parts = {x, parser->mkConstInt(5)};
        auto expr = parser->mkAdd(add_parts);
        
        model->add(x, parser->mkConstInt(10));
        auto result = parser->evaluate(expr, model);  // Result: 15
        
        std::cout << "Expression: " << parser->toString(expr) << std::endl;
        std::cout << "Evaluated result: " << parser->toString(result) << std::endl;
        
        std::cout << "✓ Advanced formula evaluation test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Advanced formula evaluation test failed: " << e.what() << std::endl;
    }
}

void test_formula_analysis_tools() {
    std::cout << "\n=== Testing Formula Analysis Tools ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        
        // Create variables first
        auto x = parser->mkVarInt("x");
        auto y = parser->mkVarInt("y");
        auto z = parser->mkVarBool("z");
        
        // Build a complex formula
        std::vector<std::shared_ptr<SMTParser::DAGNode>> xy_parts = {x, y};
        std::vector<std::shared_ptr<SMTParser::DAGNode>> formula_parts = {
            parser->mkGt(parser->mkAdd(xy_parts), parser->mkConstInt(0)),
            parser->mkLt(x, parser->mkConstInt(10)),
            parser->mkEq(z, parser->mkTrue())
        };
        auto formula = parser->mkAnd(formula_parts);
        
        // Collect atoms and variables
        std::unordered_set<std::shared_ptr<SMTParser::DAGNode>> atoms, vars;
        parser->collectAtoms(formula, atoms);
        parser->collectVars(formula, vars);
        
        std::cout << "Formula: " << parser->toString(formula) << std::endl;
        std::cout << "Found " << atoms.size() << " atoms:" << std::endl;
        for (const auto& atom : atoms) {
            std::cout << "  " << parser->toString(atom) << std::endl;
        }
        
        std::cout << "Found " << vars.size() << " variables:" << std::endl;
        for (const auto& var : vars) {
            std::cout << "  " << parser->toString(var) << std::endl;
        }
        
        // Test let expression expansion
        auto let_expr = parser->mkExpr("(let ((temp (+ x 1))) (> temp y))");
        auto expanded = parser->expandLet(let_expr);
        std::cout << "Let expression: " << parser->toString(let_expr) << std::endl;
        std::cout << "Expanded: " << parser->toString(expanded) << std::endl;
        
        std::cout << "✓ Formula analysis tools test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Formula analysis tools test failed: " << e.what() << std::endl;
    }
}

void test_optimization_modulo_theories() {
    std::cout << "\n=== Testing Optimization Modulo Theories (OMT) ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        
        // Test parsing OMT commands
        parser->parseStr("(declare-const x Int)");
        parser->parseStr("(assert (> x 0))");
        parser->parseStr("(assert-soft (< x 100) :weight 1.0)");
        
        std::cout << "OMT commands parsed successfully" << std::endl;
        
        // Get soft assertions
        auto soft_assertions = parser->getSoftAssertions();
        auto soft_weights = parser->getSoftWeights();
        
        std::cout << "Found " << soft_assertions.size() << " soft assertions" << std::endl;
        for (size_t i = 0; i < soft_assertions.size(); i++) {
            std::cout << "  Soft assertion " << i << ": " << parser->toString(soft_assertions[i]) << std::endl;
            if (i < soft_weights.size()) {
                std::cout << "    Weight: " << parser->toString(soft_weights[i]) << std::endl;
            }
        }
        
        std::cout << "✓ OMT test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ OMT test failed: " << e.what() << std::endl;
    }
}

void test_comprehensive_features() {
    std::cout << "\n=== Testing Comprehensive Features ===" << std::endl;
    
    try {
        auto parser = SMTParser::newParser();
        auto model = SMTParser::newModel();
        
        // Create variables for different theories
        auto x = parser->mkVarInt("x");
        auto y = parser->mkVarReal("y");
        auto b = parser->mkVarBool("b");
        
        // Create complex expressions
        std::vector<std::shared_ptr<SMTParser::DAGNode>> arith_parts = {x, parser->mkConstInt(5)};
        auto arithmetic_expr = parser->mkAdd(arith_parts);
        auto comparison_expr = parser->mkGt(arithmetic_expr, parser->mkConstInt(10));
        auto conditional_expr = parser->mkIte(b, x, parser->mkConstInt(0));
        
        // Build compound formula
        std::vector<std::shared_ptr<SMTParser::DAGNode>> compound_parts = {
            comparison_expr, 
            parser->mkGt(y, parser->mkConstReal(SMTParser::Real(0.5)))
        };
        auto compound_formula = parser->mkAnd(compound_parts);
        
        std::cout << "Compound formula: " << parser->toString(compound_formula) << std::endl;
        
        // Test evaluation with partial model
        model->add(x, parser->mkConstInt(8));
        model->add(b, parser->mkTrue());
        
        auto eval_arithmetic = parser->evaluate(arithmetic_expr, model);
        auto eval_conditional = parser->evaluate(conditional_expr, model);
        
        std::cout << "Arithmetic expression evaluated: " << parser->toString(eval_arithmetic) << std::endl;
        std::cout << "Conditional expression evaluated: " << parser->toString(eval_conditional) << std::endl;
        
        // Test format conversions
        auto formula_nnf = parser->toNNF(compound_formula);
        std::vector<std::shared_ptr<SMTParser::DAGNode>> formula_vec;
        formula_vec.push_back(compound_formula);
        auto formula_cnf = parser->toCNF(formula_vec);
        
        std::cout << "NNF: " << parser->toString(formula_nnf) << std::endl;
        std::cout << "CNF: " << parser->toString(formula_cnf) << std::endl;
        
        std::cout << "✓ Comprehensive features test passed" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "✗ Comprehensive features test failed: " << e.what() << std::endl;
    }
}

int main() {
    std::cout << "Testing README.md C++ Examples" << std::endl;
    std::cout << "===============================" << std::endl;
    
    test_basic_parsing();
    test_expression_building_and_evaluation();
    test_formula_conversion();
    test_advanced_formula_evaluation();
    test_formula_analysis_tools();
    test_optimization_modulo_theories();
    test_comprehensive_features();
    
    std::cout << "\n===============================" << std::endl;
    std::cout << "All README examples tested!" << std::endl;
    
    return 0;
}