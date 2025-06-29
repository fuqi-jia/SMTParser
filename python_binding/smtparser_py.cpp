/**
 * Python bindings for SMTParser library using pybind11
 * 
 * This file provides Python bindings for the core SMTParser functionality
 * including parsing, expression building, and model evaluation.
 * 
 * Author: SMTParser Python Binding
 * License: MIT
 */

#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/operators.h>
#include <pybind11/functional.h>

#include "parser.h"
#include "dag.h"
#include "model.h"
#include "objective.h"
#include "sort.h"
#include "kind.h"

namespace py = pybind11;
using namespace SMTParser;

PYBIND11_MODULE(smtparser, m) {
    m.doc() = "SMT-LIB2 Parser and Expression Builder Library";
    
    // Expose RESULT_TYPE enum
    py::enum_<RESULT_TYPE>(m, "ResultType")
        .value("SAT", RESULT_TYPE::RT_SAT)
        .value("UNSAT", RESULT_TYPE::RT_UNSAT)
        .value("DELTA_SAT", RESULT_TYPE::RT_DELTA_SAT)
        .value("UNKNOWN", RESULT_TYPE::RT_UNKNOWN)
        .value("ERROR", RESULT_TYPE::RT_ERROR);
    
    // Expose NODE_KIND enum (partial, most commonly used)
    py::enum_<NODE_KIND>(m, "NodeKind")
        .value("VAR", NODE_KIND::NT_VAR)
        .value("CONST", NODE_KIND::NT_CONST)
        .value("CONST_TRUE", NODE_KIND::NT_CONST_TRUE)
        .value("CONST_FALSE", NODE_KIND::NT_CONST_FALSE)
        .value("AND", NODE_KIND::NT_AND)
        .value("OR", NODE_KIND::NT_OR)
        .value("NOT", NODE_KIND::NT_NOT)
        .value("IMPLIES", NODE_KIND::NT_IMPLIES)
        .value("XOR", NODE_KIND::NT_XOR)
        .value("EQ", NODE_KIND::NT_EQ)
        .value("DISTINCT", NODE_KIND::NT_DISTINCT)
        .value("ADD", NODE_KIND::NT_ADD)
        .value("SUB", NODE_KIND::NT_SUB)
        .value("MUL", NODE_KIND::NT_MUL)
        .value("DIV_INT", NODE_KIND::NT_DIV_INT)
        .value("DIV_REAL", NODE_KIND::NT_DIV_REAL)
        .value("MOD", NODE_KIND::NT_MOD)
        .value("NEG", NODE_KIND::NT_NEG)
        .value("LT", NODE_KIND::NT_LT)
        .value("LE", NODE_KIND::NT_LE)
        .value("GT", NODE_KIND::NT_GT)
        .value("GE", NODE_KIND::NT_GE)
        .value("ITE", NODE_KIND::NT_ITE);
    
    // Expose OPT_KIND enum
    py::enum_<OPT_KIND>(m, "OptKind")
        .value("MINIMIZE", OPT_KIND::OPT_MINIMIZE)
        .value("MAXIMIZE", OPT_KIND::OPT_MAXIMIZE)
        .value("MAXSAT", OPT_KIND::OPT_MAXSAT)
        .value("MINSAT", OPT_KIND::OPT_MINSAT)
        .value("LEX_OPTIMIZE", OPT_KIND::OPT_LEX_OPTIMIZE)
        .value("PARETO_OPTIMIZE", OPT_KIND::OPT_PARETO_OPTIMIZE)
        .value("BOX_OPTIMIZE", OPT_KIND::OPT_BOX_OPTIMIZE)
        .value("MINMAX", OPT_KIND::OPT_MINMAX)
        .value("MAXMIN", OPT_KIND::OPT_MAXMIN);
    
    // Expose Sort class
    py::class_<Sort, std::shared_ptr<Sort>>(m, "Sort")
        .def("isBool", &Sort::isBool)
        .def("isInt", &Sort::isInt)
        .def("isReal", &Sort::isReal)
        .def("isArray", &Sort::isArray)
        .def("isBv", &Sort::isBv)
        .def("isFp", &Sort::isFp)
        .def("isStr", &Sort::isStr)
        .def("toString", &Sort::toString);
    
    // Expose DAGNode class
    py::class_<DAGNode, std::shared_ptr<DAGNode>>(m, "DAGNode")
        .def("getKind", &DAGNode::getKind)
        .def("getSort", &DAGNode::getSort)
        .def("getName", &DAGNode::getName)
        .def("getChildrenSize", &DAGNode::getChildrenSize)
        .def("getChild", &DAGNode::getChild)
        .def("getChildren", &DAGNode::getChildren)
        .def("isLeaf", &DAGNode::isLeaf)
        .def("isInternal", &DAGNode::isInternal)
        .def("isVar", &DAGNode::isVar)
        .def("isConst", &DAGNode::isConst)
        .def("isTrue", &DAGNode::isTrue)
        .def("isFalse", &DAGNode::isFalse)
        .def("isAnd", &DAGNode::isAnd)
        .def("isOr", &DAGNode::isOr)
        .def("isNot", &DAGNode::isNot)
        .def("isEq", &DAGNode::isEq)
        .def("isAdd", &DAGNode::isAdd)
        .def("isSub", &DAGNode::isSub)
        .def("isMul", &DAGNode::isMul)
        .def("isLt", &DAGNode::isLt)
        .def("isLe", &DAGNode::isLe)
        .def("isGt", &DAGNode::isGt)
        .def("isGe", &DAGNode::isGe)
        .def("isIte", &DAGNode::isIte)
        .def("hashString", &DAGNode::hashString);
    
    // Expose Model class
    py::class_<Model, std::shared_ptr<Model>>(m, "Model")
        .def(py::init<>())
        .def("add", py::overload_cast<const std::shared_ptr<DAGNode>&, const std::shared_ptr<DAGNode>&>(&Model::add))
        .def("add", py::overload_cast<const std::string&, const std::shared_ptr<DAGNode>&>(&Model::add))
        .def("addVar", &Model::addVar)
        .def("get", py::overload_cast<const std::shared_ptr<DAGNode>&>(&Model::get))
        .def("get", py::overload_cast<const std::string&>(&Model::get))
        .def("isFull", &Model::isFull)
        .def("isEmpty", &Model::isEmpty)
        .def("clear", &Model::clear)
        .def("clearValues", &Model::clearValues)
        .def("size", &Model::size)
        .def("getVars", &Model::getVars)
        .def("getValues", &Model::getValues)
        .def("getPairs", &Model::getPairs)
        .def("toString", &Model::toString);
    
    // Expose Objective classes
    py::class_<MetaObjective, std::shared_ptr<MetaObjective>>(m, "MetaObjective")
        .def("getGroupID", &MetaObjective::getGroupID)
        .def("getObjectiveKind", &MetaObjective::getObjectiveKind)
        .def("isSingleObjective", &MetaObjective::isSingleObjective)
        .def("isMultiObjective", &MetaObjective::isMultiObjective)
        .def("isMaximize", &MetaObjective::isMaximize)
        .def("isMinimize", &MetaObjective::isMinimize)
        .def("getObjectiveTerm", &MetaObjective::getObjectiveTerm)
        .def("getObjectiveSize", &MetaObjective::getObjectiveSize);
    
    py::class_<SingleObjective, MetaObjective, std::shared_ptr<SingleObjective>>(m, "SingleObjective");
    py::class_<Objective, MetaObjective, std::shared_ptr<Objective>>(m, "Objective");
    
    // Expose Parser class - the main API
    py::class_<Parser>(m, "Parser")
        .def(py::init<>(), "Create empty parser")
        .def(py::init<const std::string&>(), "Create parser and parse file")
        
        // File parsing methods
        .def("parse", &Parser::parse, "Parse SMT-LIB2 file")
        .def("parseStr", &Parser::parseStr, "Parse constraint string")
        .def("assert", py::overload_cast<const std::string&>(&Parser::assert), "Assert constraint from string")
        .def("assert", py::overload_cast<std::shared_ptr<DAGNode>>(&Parser::assert), "Assert constraint from DAGNode")
        .def("mkExpr", &Parser::mkExpr, "Create DAG node from string expression")
        
        // Getter methods
        .def("getAssertions", &Parser::getAssertions, "Get all assertions")
        .def("getGroupedAssertions", &Parser::getGroupedAssertions, "Get grouped assertions")
        .def("getAssumptions", &Parser::getAssumptions, "Get assumptions")
        .def("getSoftAssertions", &Parser::getSoftAssertions, "Get soft assertions")
        .def("getSoftWeights", &Parser::getSoftWeights, "Get soft assertion weights")
        .def("getGroupedSoftAssertions", &Parser::getGroupedSoftAssertions, "Get grouped soft assertions")
        .def("getObjectives", &Parser::getObjectives, "Get objectives")
        .def("getVariables", &Parser::getVariables, "Get all variables")
        .def("getDeclaredVariables", &Parser::getDeclaredVariables, "Get declared variables")
        .def("getVariable", &Parser::getVariable, "Get variable by name")
        .def("getFunctions", &Parser::getFunctions, "Get all functions")
        
        // Expression building methods
        .def("mkOper", py::overload_cast<const std::shared_ptr<Sort>&, const NODE_KIND&, std::shared_ptr<DAGNode>>(&Parser::mkOper), "Create unary operation")
        .def("mkOper", py::overload_cast<const std::shared_ptr<Sort>&, const NODE_KIND&, std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkOper), "Create binary operation")
        .def("mkOper", py::overload_cast<const std::shared_ptr<Sort>&, const NODE_KIND&, std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkOper), "Create ternary operation")
        .def("mkOper", py::overload_cast<const std::shared_ptr<Sort>&, const NODE_KIND&, const std::vector<std::shared_ptr<DAGNode>>&>(&Parser::mkOper), "Create n-ary operation")
        
        // Specific expression builders
        .def("mkVar", &Parser::mkVar, "Create variable")
        .def("mkVarBool", &Parser::mkVarBool, "Create boolean variable")
        .def("mkVarInt", &Parser::mkVarInt, "Create integer variable")
        .def("mkVarReal", &Parser::mkVarReal, "Create real variable")
        .def("mkConstInt", &Parser::mkConstInt, "Create integer constant")
        .def("mkConstReal", &Parser::mkConstReal, "Create real constant")
        .def("mkConstBool", &Parser::mkConstBool, "Create boolean constant")
        .def("mkTrue", &Parser::mkTrue, "Create true constant")
        .def("mkFalse", &Parser::mkFalse, "Create false constant")
        
        // Boolean operations
        .def("mkAnd", py::overload_cast<const std::vector<std::shared_ptr<DAGNode>>&>(&Parser::mkAnd), "Create AND operation")
        .def("mkAnd", py::overload_cast<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkAnd), "Create binary AND")
        .def("mkOr", py::overload_cast<const std::vector<std::shared_ptr<DAGNode>>&>(&Parser::mkOr), "Create OR operation")
        .def("mkOr", py::overload_cast<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkOr), "Create binary OR")
        .def("mkNot", &Parser::mkNot, "Create NOT operation")
        .def("mkImplies", &Parser::mkImplies, "Create IMPLIES operation")
        .def("mkXor", &Parser::mkXor, "Create XOR operation")
        .def("mkEq", &Parser::mkEq, "Create equality")
        .def("mkDistinct", &Parser::mkDistinct, "Create distinct")
        .def("mkIte", &Parser::mkIte, "Create if-then-else")
        
        // Arithmetic operations
        .def("mkAdd", py::overload_cast<const std::vector<std::shared_ptr<DAGNode>>&>(&Parser::mkAdd), "Create addition")
        .def("mkAdd", py::overload_cast<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkAdd), "Create binary addition")
        .def("mkSub", &Parser::mkSub, "Create subtraction")
        .def("mkMul", py::overload_cast<const std::vector<std::shared_ptr<DAGNode>>&>(&Parser::mkMul), "Create multiplication")
        .def("mkMul", py::overload_cast<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>(&Parser::mkMul), "Create binary multiplication")
        .def("mkDiv", &Parser::mkDiv, "Create division")
        .def("mkMod", &Parser::mkMod, "Create modulo")
        .def("mkNeg", &Parser::mkNeg, "Create negation")
        .def("mkAbs", &Parser::mkAbs, "Create absolute value")
        
        // Comparison operations
        .def("mkLt", &Parser::mkLt, "Create less than")
        .def("mkLe", &Parser::mkLe, "Create less than or equal")
        .def("mkGt", &Parser::mkGt, "Create greater than")
        .def("mkGe", &Parser::mkGe, "Create greater than or equal")
        
        // Utility methods
        .def("toString", &Parser::toString, "Convert DAG node to string")
        .def("evaluate", py::overload_cast<std::shared_ptr<DAGNode>, const std::shared_ptr<Model>&>(&Parser::evaluate), "Evaluate expression with model")
        .def("checkSat", &Parser::checkSat, "Check satisfiability")
        .def("getResultType", &Parser::getResultType, "Get result type")
        .def("getResult", &Parser::getResult, "Get result")
        .def("getModel", &Parser::getModel, "Get model")
        .def("dumpSMT2", py::overload_cast<>(&Parser::dumpSMT2), "Dump to SMT-LIB2 format");
    
    // Factory functions
    m.def("newParser", py::overload_cast<>(&SMTParser::newParser), "Create new parser");
    m.def("newParser", py::overload_cast<const std::string&>(&SMTParser::newParser), "Create new parser with file");
    m.def("newModel", &SMTParser::newModel, "Create new model");
    
    // Global sort constants
    m.attr("BOOL_SORT") = BOOL_SORT;
    m.attr("INT_SORT") = INT_SORT;
    m.attr("REAL_SORT") = REAL_SORT;
    m.attr("NULL_SORT") = NULL_SORT;
    
    // Global node constants
    m.attr("NULL_NODE") = NULL_NODE;
    m.attr("TRUE_NODE") = TRUE_NODE;
    m.attr("FALSE_NODE") = FALSE_NODE;
} 