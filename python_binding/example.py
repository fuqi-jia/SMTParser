#!/usr/bin/env python3
"""
Example usage of SMTParser Python bindings

This example demonstrates how to:
1. Parse SMT-LIB2 files
2. Build expressions programmatically
3. Evaluate expressions with models
4. Work with different SMT theories

Requirements:
- smtparser Python module (built from this package)
"""

import smtparser

def example_parsing():
    """Example of parsing SMT-LIB2 files"""
    print("=== SMT-LIB2 File Parsing Example ===")
    
    # Create a parser
    parser = smtparser.Parser()
    
    # Parse a simple constraint string
    success = parser.parseStr("(declare-fun x () Int)")
    if success:
        print("Successfully parsed variable declaration")
    
    # Assert some constraints
    parser.assert_("(assert (> x 0))")
    parser.assert_("(assert (< x 10))")
    
    # Get assertions
    assertions = parser.getAssertions()
    print(f"Number of assertions: {len(assertions)}")
    
    # Print each assertion
    for i, assertion in enumerate(assertions):
        print(f"Assertion {i+1}: {parser.toString(assertion)}")

def example_expression_building():
    """Example of building expressions programmatically"""
    print("\n=== Expression Building Example ===")
    
    # Create parser
    parser = smtparser.Parser()
    
    # Create variables
    x = parser.mkVarInt("x")
    y = parser.mkVarInt("y")
    
    print(f"Created variables: x = {parser.toString(x)}, y = {parser.toString(y)}")
    
    # Create constants
    const_5 = parser.mkConstInt(5)
    const_10 = parser.mkConstInt(10)
    
    # Build expressions
    sum_expr = parser.mkAdd(x, y)  # x + y
    constraint1 = parser.mkGt(sum_expr, const_5)  # (x + y) > 5
    constraint2 = parser.mkLt(x, const_10)  # x < 10
    
    print(f"Expression 1: {parser.toString(constraint1)}")
    print(f"Expression 2: {parser.toString(constraint2)}")
    
    # Combine with AND
    combined = parser.mkAnd(constraint1, constraint2)
    print(f"Combined: {parser.toString(combined)}")
    
    # Assert the combined constraint
    parser.assert_(combined)

def example_boolean_operations():
    """Example of boolean operations"""
    print("\n=== Boolean Operations Example ===")
    
    parser = smtparser.Parser()
    
    # Create boolean variables
    p = parser.mkVarBool("p")
    q = parser.mkVarBool("q")
    r = parser.mkVarBool("r")
    
    # Create boolean expressions
    and_expr = parser.mkAnd(p, q)
    or_expr = parser.mkOr(p, q)
    not_expr = parser.mkNot(p)
    implies_expr = parser.mkImplies(p, q)
    ite_expr = parser.mkIte(p, q, r)  # if p then q else r
    
    print(f"AND: {parser.toString(and_expr)}")
    print(f"OR: {parser.toString(or_expr)}")
    print(f"NOT: {parser.toString(not_expr)}")
    print(f"IMPLIES: {parser.toString(implies_expr)}")
    print(f"ITE: {parser.toString(ite_expr)}")

def example_model_evaluation():
    """Example of model evaluation"""
    print("\n=== Model Evaluation Example ===")
    
    parser = smtparser.Parser()
    
    # Create variables and expressions
    x = parser.mkVarInt("x")
    y = parser.mkVarInt("y")
    expr = parser.mkAdd(x, y)
    
    # Create a model
    model = smtparser.newModel()
    
    # Add assignments to model
    model.add(x, parser.mkConstInt(10))
    model.add(y, parser.mkConstInt(20))
    
    print(f"Model size: {model.size()}")
    print(f"Model: {model.toString()}")
    
    # Evaluate expression with model
    result = parser.evaluate(expr, model)
    print(f"Expression: {parser.toString(expr)}")
    print(f"Evaluated result: {parser.toString(result)}")

def example_working_with_sorts():
    """Example of working with sorts (types)"""
    print("\n=== Working with Sorts Example ===")
    
    parser = smtparser.Parser()
    
    # Create variables of different sorts
    bool_var = parser.mkVarBool("b")
    int_var = parser.mkVarInt("i")
    real_var = parser.mkVarReal("r")
    
    # Get and examine sorts
    bool_sort = bool_var.getSort()
    int_sort = int_var.getSort()
    real_sort = real_var.getSort()
    
    print(f"Boolean sort: {bool_sort.toString()}, isBool: {bool_sort.isBool()}")
    print(f"Integer sort: {int_sort.toString()}, isInt: {int_sort.isInt()}")
    print(f"Real sort: {real_sort.toString()}, isReal: {real_sort.isReal()}")
    
    # Use predefined sorts
    print(f"BOOL_SORT: {smtparser.BOOL_SORT.toString()}")
    print(f"INT_SORT: {smtparser.INT_SORT.toString()}")
    print(f"REAL_SORT: {smtparser.REAL_SORT.toString()}")

def example_node_properties():
    """Example of examining node properties"""
    print("\n=== Node Properties Example ===")
    
    parser = smtparser.Parser()
    
    # Create different types of nodes
    var = parser.mkVarInt("x")
    const = parser.mkConstInt(42)
    expr = parser.mkAdd(var, const)
    
    print(f"Variable '{parser.toString(var)}':")
    print(f"  - isVar: {var.isVar()}")
    print(f"  - isConst: {var.isConst()}")
    print(f"  - isLeaf: {var.isLeaf()}")
    print(f"  - Kind: {var.getKind()}")
    
    print(f"Constant '{parser.toString(const)}':")
    print(f"  - isVar: {const.isVar()}")
    print(f"  - isConst: {const.isConst()}")
    print(f"  - isLeaf: {const.isLeaf()}")
    
    print(f"Expression '{parser.toString(expr)}':")
    print(f"  - isAdd: {expr.isAdd()}")
    print(f"  - isLeaf: {expr.isLeaf()}")
    print(f"  - isInternal: {expr.isInternal()}")
    print(f"  - Children count: {expr.getChildrenSize()}")
    print(f"  - Child 0: {parser.toString(expr.getChild(0))}")
    print(f"  - Child 1: {parser.toString(expr.getChild(1))}")

def example_factory_functions():
    """Example of using factory functions"""
    print("\n=== Factory Functions Example ===")
    
    # Using factory functions (alternative way to create objects)
    parser = smtparser.newParser()
    model = smtparser.newModel()
    
    print("Created parser and model using factory functions")
    
    # You can also create parser with a file
    # parser_with_file = smtparser.newParser("formula.smt2")

def main():
    """Run all examples"""
    print("SMTParser Python Bindings Examples")
    print("=" * 50)
    
    try:
        example_parsing()
        example_expression_building()
        example_boolean_operations()
        example_model_evaluation()
        example_working_with_sorts()
        example_node_properties()
        example_factory_functions()
        
        print("\n=== All Examples Completed Successfully ===")
        
    except Exception as e:
        print(f"Error running examples: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main() 