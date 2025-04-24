/* -*- Source -*-
 *
 * The Directed Acyclic Graph (DAG) Class
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include "../include/dag.h"
#include <stack>
#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>
namespace SMTLIBParser{

    void DAGNode::updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        assert(out_sort == sort);
        children.clear();
        children.push_back(body);
        for(auto& p : params){
            children.push_back(p);
        }
        kind = NODE_KIND::NT_FUNC_DEF;
    }

    
    void DAGNode::updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        assert(out_sort == sort);
        children.clear();
        children.push_back(body);
        for(auto& p : params){
            children.push_back(p);
        }
        kind = NODE_KIND::NT_FUNC_APPLY;
    }

    std::string dumpConst(const std::string& name, const std::shared_ptr<Sort>& sort){
        if(sort->isReal()){
            if(name[0] == '-'){
                return "(- " + name.substr(1) + ")";
            }
            else{
                return name;
            }
        }
        else if(sort->isRat()){
            size_t pos = name.find("/");
            if(pos == std::string::npos){
                return name;
            }
            std::string num = name.substr(0, pos);
            std::string den = name.substr(pos+1);
            bool is_neg = false;
            if(num[0] == '-'){
                is_neg = true;
                num = num.substr(1);
            }
            if(den[0] == '-'){
                is_neg = !is_neg;
                den = den.substr(1);
            }
            if(is_neg){
                return "(/ (- " + num + ") " + den + ")";
            }
            else{
                return "(/ " + num + " " + den + ")";
            }
        }
        else if(sort->isInt()){
            if(name[0] == '-'){
                return "(- " + name.substr(1) + ")";
            }
            else{
                return name;
            }
        }
        else if(sort->isBool()){}
        else if(sort->isBv()){}
        else if(sort->isFp()){}
        else if(sort->isStr()){}
        else if(sort->isArray()){}
        return name;
    }


    // Iterative version of dumpSMTLIB2 function, avoid stack overflow
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& root) {
        if (!root) return "";
        
        // Cache results, avoid duplicate processing
        boost::unordered_map<std::shared_ptr<DAGNode>, std::string> results;
        
        // Stack for post-order traversal
        std::stack<std::shared_ptr<DAGNode>> todo;
        
        // Cache visited nodes, avoid duplicate addition to stack
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        
        // Record processing status of each node (used to determine if all children are processed)
        boost::unordered_map<std::shared_ptr<DAGNode>, bool> processed;
        
        // Initialize stack, start from root node
        todo.push(root);
        
        while (!todo.empty()) {
            std::shared_ptr<DAGNode> current = todo.top();
            
            // If current node has been processed, pop it
            if (results.find(current) != results.end()) {
                todo.pop();
                continue;
            }
            
            // If current node is visited for the first time, mark it as visited
            if (visited.find(current) == visited.end()) {
                visited.insert(current);
                processed[current] = false;
            }
            
            // If all children are processed, process current node
            if (processed[current]) {
                std::string res = "";
                auto kind = current->getKind();
                
                switch (kind) {
                // Basic type and constant processing
                case NODE_KIND::NT_UNKNOWN:
                    std::cerr << "遇到未知类型节点" << std::endl;
                    assert(false);
                    break;
                case NODE_KIND::NT_ERROR:
                    std::cerr << "遇到错误类型节点" << std::endl;
                    assert(false);
                    break;
                case NODE_KIND::NT_NULL:
                    std::cerr << "遇到空类型节点" << std::endl;
                    assert(false);
                    res = "NULL";
                    break;
                case NODE_KIND::NT_CONST_TRUE:
                    res = "true";
                    break;
                case NODE_KIND::NT_CONST_FALSE:
                    res = "false";
                    break;
                
                // Constant and variable
                case NODE_KIND::NT_CONST:
                    res = dumpConst(current->getName(), current->getSort());
                    break;
                case NODE_KIND::NT_VAR:
                    res = current->getName();
                    break;
                    
                // Unary operation - accepts one parameter
                case NODE_KIND::NT_NOT:
                case NODE_KIND::NT_NEG:
                case NODE_KIND::NT_ABS:
                case NODE_KIND::NT_SQRT:
                case NODE_KIND::NT_CEIL:
                case NODE_KIND::NT_FLOOR:
                case NODE_KIND::NT_ROUND:
                case NODE_KIND::NT_EXP:
                case NODE_KIND::NT_LN:
                case NODE_KIND::NT_LG:
                case NODE_KIND::NT_SIN:
                case NODE_KIND::NT_COS:
                case NODE_KIND::NT_SEC:
                case NODE_KIND::NT_CSC:
                case NODE_KIND::NT_TAN:
                case NODE_KIND::NT_COT:
                case NODE_KIND::NT_ASIN:
                case NODE_KIND::NT_ACOS:
                case NODE_KIND::NT_ASEC:
                case NODE_KIND::NT_ACSC:
                case NODE_KIND::NT_ATAN:
                case NODE_KIND::NT_ACOT:
                case NODE_KIND::NT_SINH:
                case NODE_KIND::NT_COSH:
                case NODE_KIND::NT_TANH:
                case NODE_KIND::NT_SECH:
                case NODE_KIND::NT_CSCH:
                case NODE_KIND::NT_COTH:
                case NODE_KIND::NT_ASINH:
                case NODE_KIND::NT_ACOSH:
                case NODE_KIND::NT_ATANH:
                case NODE_KIND::NT_ASECH:
                case NODE_KIND::NT_ACSCH:
                case NODE_KIND::NT_ACOTH:
                case NODE_KIND::NT_TO_INT:
                case NODE_KIND::NT_TO_REAL:
                case NODE_KIND::NT_IS_INT:
                case NODE_KIND::NT_IS_PRIME:
                case NODE_KIND::NT_IS_EVEN:
                case NODE_KIND::NT_IS_ODD:
                case NODE_KIND::NT_FACT:
                case NODE_KIND::NT_BV_NOT:
                case NODE_KIND::NT_BV_NEG:
                case NODE_KIND::NT_BV_NEGO:
                case NODE_KIND::NT_FP_ABS:
                case NODE_KIND::NT_FP_NEG:
                case NODE_KIND::NT_FP_SQRT:
                case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
                case NODE_KIND::NT_FP_IS_NORMAL:
                case NODE_KIND::NT_FP_IS_SUBNORMAL:
                case NODE_KIND::NT_FP_IS_ZERO:
                case NODE_KIND::NT_FP_IS_INF:
                case NODE_KIND::NT_FP_IS_NAN:
                case NODE_KIND::NT_FP_IS_NEG:
                case NODE_KIND::NT_FP_IS_POS:
                case NODE_KIND::NT_FP_TO_UBV:
                case NODE_KIND::NT_FP_TO_SBV:
                case NODE_KIND::NT_FP_TO_REAL:
                case NODE_KIND::NT_FP_TO_FP:
                case NODE_KIND::NT_STR_LEN:
                case NODE_KIND::NT_STR_TO_LOWER:
                case NODE_KIND::NT_STR_TO_UPPER:
                case NODE_KIND::NT_STR_REV:
                case NODE_KIND::NT_STR_IS_DIGIT:
                case NODE_KIND::NT_STR_FROM_INT:
                case NODE_KIND::NT_STR_TO_INT:
                case NODE_KIND::NT_STR_TO_REG:
                case NODE_KIND::NT_STR_TO_CODE:
                case NODE_KIND::NT_STR_FROM_CODE:
                case NODE_KIND::NT_REG_STAR:
                case NODE_KIND::NT_REG_PLUS:
                case NODE_KIND::NT_REG_OPT:
                case NODE_KIND::NT_REG_COMPLEMENT:
                case NODE_KIND::NT_BV_TO_NAT:
                case NODE_KIND::NT_NAT_TO_BV:
                case NODE_KIND::NT_POW2:
                    res = "(" + kindToString(kind) + " " + results[current->getChild(0)] + ")";
                    break;
                    
                // Binary operation - accepts two parameters
                case NODE_KIND::NT_EQ:
                case NODE_KIND::NT_EQ_BOOL:
                case NODE_KIND::NT_EQ_OTHER:
                case NODE_KIND::NT_POW:
                case NODE_KIND::NT_DIV_INT:
                case NODE_KIND::NT_DIV_REAL:
                case NODE_KIND::NT_MOD:
                case NODE_KIND::NT_LOG:
                case NODE_KIND::NT_LE:
                case NODE_KIND::NT_LT:
                case NODE_KIND::NT_GE:
                case NODE_KIND::NT_GT:
                case NODE_KIND::NT_IS_DIVISIBLE:
                case NODE_KIND::NT_GCD:
                case NODE_KIND::NT_LCM:
                case NODE_KIND::NT_BV_UDIV:
                case NODE_KIND::NT_BV_SDIV:
                case NODE_KIND::NT_BV_UREM:
                case NODE_KIND::NT_BV_SREM:
                case NODE_KIND::NT_BV_UMOD:
                case NODE_KIND::NT_BV_SMOD:
                case NODE_KIND::NT_BV_SDIVO:
                case NODE_KIND::NT_BV_UDIVO:
                case NODE_KIND::NT_BV_SREMO:
                case NODE_KIND::NT_BV_UREMO:
                case NODE_KIND::NT_BV_SMODO:
                case NODE_KIND::NT_BV_UMODO:
                case NODE_KIND::NT_BV_SHL:
                case NODE_KIND::NT_BV_LSHR:
                case NODE_KIND::NT_BV_ASHR:
                case NODE_KIND::NT_BV_ULT:
                case NODE_KIND::NT_BV_ULE:
                case NODE_KIND::NT_BV_UGT:
                case NODE_KIND::NT_BV_UGE:
                case NODE_KIND::NT_BV_SLT:
                case NODE_KIND::NT_BV_SLE:
                case NODE_KIND::NT_BV_SGT:
                case NODE_KIND::NT_BV_SGE:
                case NODE_KIND::NT_FP_DIV:
                case NODE_KIND::NT_FP_REM:
                case NODE_KIND::NT_FP_LE:
                case NODE_KIND::NT_FP_LT:
                case NODE_KIND::NT_FP_GE:
                case NODE_KIND::NT_FP_GT:
                case NODE_KIND::NT_FP_EQ:
                case NODE_KIND::NT_SELECT:
                case NODE_KIND::NT_STR_PREFIXOF:
                case NODE_KIND::NT_STR_SUFFIXOF:
                case NODE_KIND::NT_STR_CHARAT:
                case NODE_KIND::NT_STR_SPLIT:
                case NODE_KIND::NT_STR_LT:
                case NODE_KIND::NT_STR_LE:
                case NODE_KIND::NT_STR_GT:
                case NODE_KIND::NT_STR_GE:
                case NODE_KIND::NT_STR_IN_REG:
                case NODE_KIND::NT_STR_CONTAINS:
                case NODE_KIND::NT_REG_RANGE:
                case NODE_KIND::NT_REG_REPEAT:
                    res = "(" + kindToString(kind) + " " + results[current->getChild(0)] + " " + results[current->getChild(1)] + ")";
                    break;
                    
                // Ternary operation - accepts three parameters
                case NODE_KIND::NT_ITE:
                case NODE_KIND::NT_FP_FMA:
                case NODE_KIND::NT_STORE:
                case NODE_KIND::NT_STR_SUBSTR:
                case NODE_KIND::NT_STR_INDEXOF:
                case NODE_KIND::NT_STR_UPDATE:
                case NODE_KIND::NT_STR_REPLACE:
                case NODE_KIND::NT_STR_REPLACE_ALL:
                case NODE_KIND::NT_REG_LOOP:
                case NODE_KIND::NT_REPLACE_REG:
                case NODE_KIND::NT_REPLACE_REG_ALL:
                case NODE_KIND::NT_INDEXOF_REG:
                    res = "(" + kindToString(kind) + " " + results[current->getChild(0)] + " " + results[current->getChild(1)] + " " + results[current->getChild(2)] + ")";
                    break;
                    
                // Multi-parameter operation - accepts arbitrary number of parameters
                case NODE_KIND::NT_DISTINCT:
                case NODE_KIND::NT_DISTINCT_BOOL:
                case NODE_KIND::NT_DISTINCT_OTHER:
                case NODE_KIND::NT_AND:
                case NODE_KIND::NT_OR:
                case NODE_KIND::NT_IMPLIES:
                case NODE_KIND::NT_XOR:
                case NODE_KIND::NT_ADD:
                case NODE_KIND::NT_MUL:
                case NODE_KIND::NT_IAND:
                case NODE_KIND::NT_SUB:
                case NODE_KIND::NT_BV_AND:
                case NODE_KIND::NT_BV_OR:
                case NODE_KIND::NT_BV_XOR:
                case NODE_KIND::NT_BV_NAND:
                case NODE_KIND::NT_BV_NOR:
                case NODE_KIND::NT_BV_XNOR:
                case NODE_KIND::NT_BV_COMP:
                case NODE_KIND::NT_BV_ADD:
                case NODE_KIND::NT_BV_SUB:
                case NODE_KIND::NT_BV_MUL:
                case NODE_KIND::NT_BV_SADDO:
                case NODE_KIND::NT_BV_UADDO:
                case NODE_KIND::NT_BV_SMULO:
                case NODE_KIND::NT_BV_UMULO:
                case NODE_KIND::NT_BV_CONCAT:
                case NODE_KIND::NT_FP_ADD:
                case NODE_KIND::NT_FP_SUB:
                case NODE_KIND::NT_FP_MUL:
                case NODE_KIND::NT_FP_MIN:
                case NODE_KIND::NT_FP_MAX:
                case NODE_KIND::NT_STR_CONCAT:
                case NODE_KIND::NT_REG_CONCAT:
                case NODE_KIND::NT_REG_UNION:
                case NODE_KIND::NT_REG_INTER:
                case NODE_KIND::NT_REG_DIFF: {
                    res = "(" + kindToString(kind);
                    for (auto& child : current->getChildren()) {
                        res += " " + results[child];
                    }
                    res += ")";
                    break;
                }
                    
                // Special processing operation
                case NODE_KIND::NT_BV_EXTRACT:
                    res = "((_ extract " + results[current->getChild(1)] + " " + results[current->getChild(2)] + ") " + results[current->getChild(0)] + ")";
                    break;
                    
                case NODE_KIND::NT_BV_REPEAT:
                case NODE_KIND::NT_BV_ZERO_EXT:
                case NODE_KIND::NT_BV_SIGN_EXT:
                case NODE_KIND::NT_BV_ROTATE_LEFT:
                case NODE_KIND::NT_BV_ROTATE_RIGHT:
                    res = "((_ " + kindToString(kind) + " " + results[current->getChild(1)] + ") " + results[current->getChild(0)] + ")";
                    break;
                    
                // Constant
                case NODE_KIND::NT_PI:
                    res = "pi";
                    break;
                case NODE_KIND::NT_E:
                    res = "e";
                    break;
                case NODE_KIND::NT_INFINITY:
                    res = "inf";
                    break;
                case NODE_KIND::NT_NAN:
                    res = "NaN";
                    break;
                case NODE_KIND::NT_EPSILON:
                    res = "epsilon";
                    break;
                case NODE_KIND::NT_REG_NONE:
                    res = "re.none";
                    break;
                case NODE_KIND::NT_REG_ALL:
                    res = "re.all";
                    break;
                case NODE_KIND::NT_REG_ALLCHAR:
                    res = "re.allchar";
                    break;
                    
                // Quantifier
                case NODE_KIND::NT_FORALL:
                case NODE_KIND::NT_EXISTS: {
                    res = "(" + kindToString(kind) + " (";
                    for (size_t i = 1; i < current->getChildrenSize(); i++) {
                        if (i == 1) 
                            res += "(" + results[current->getChild(i)] + " " + current->getChild(i)->getSort()->toString() + ")";
                        else 
                            res += " (" + results[current->getChild(i)] + " " + current->getChild(i)->getSort()->toString() + ")";
                    }
                    res += ") ";
                    res += results[current->getChild(0)];
                    res += ")";
                    break;
                }
                
                case NODE_KIND::NT_QUANT_VAR:
                    res = current->getName();
                    break;
                    
                // Function related
                case NODE_KIND::NT_FUNC_DEC:
                case NODE_KIND::NT_FUNC_DEF:
                case NODE_KIND::NT_FUNC_PARAM:
                    res = current->getName();
                    break;
                    
                case NODE_KIND::NT_FUNC_APPLY: {
                    res = "(" + current->getName();
                    for (size_t i = 1; i < current->getChildrenSize(); i++) {
                        res += " " + results[current->getChild(i)];
                    }
                    res += ")";
                    break;
                }
                
                case NODE_KIND::NT_LET:
                    res = results[current->getChild(0)];
                    break;
                    
                case NODE_KIND::NT_APPLY_UF:
                    res = "(" + current->getName();
                    for (auto& child : current->getChildren()) {
                        res += " " + results[child];
                    }
                    res += ")";
                    break;
                    
                default:
                    std::cerr << "未知操作符类型：" << static_cast<int>(kind) << std::endl;
                    res = "UNKNOWN_KIND";
                }
                
                results[current] = res;
                todo.pop();
                continue;
            }
            
            // Determine if child nodes need to be added
            bool allChildrenProcessed = true;
            for (auto& child : current->getChildren()) {
                if (results.find(child) == results.end()) {
                    allChildrenProcessed = false;
                    todo.push(child);
                }
            }
            
            if (!allChildrenProcessed) {
                // If there are unprocessed child nodes, wait for all child nodes to be processed
                processed[current] = false;
            } else {
                // If all child nodes have been processed, mark the current node as processed
                processed[current] = true;
            }
        }
        
        return results[root];
    }
    
    std::string dumpFuncDef(const std::shared_ptr<DAGNode>& node){
        std::string res = "(define-fun " + node->getName() + " (";
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i==1) res += "(" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
            else res += " (" + node->getChild(i)->getName() +" " + node->getChild(i)->getSort()->toString() +")";
        }
        res += ") " + node->getChild(0)->getSort()->toString() + " ";
        res += dumpSMTLIB2(node->getChild(0)) +  ")";
        return res;
    }
    std::string dumpFuncDec(const std::shared_ptr<DAGNode>& node){
        std::string res = "(declare-fun " + node->getName() + " (";
        for(size_t i=1;i<node->getChildrenSize();i++){
            if(i==1) res += node->getChild(i)->getSort()->toString();
            else res += " " + node->getChild(i)->getSort()->toString();
        }
        res += ") " + node->getChild(0)->getSort()->toString() + ")";
        return res;
    }
    std::string dumpSMTLIB2(const std::vector<std::shared_ptr<DAGNode>>& assertions){
        std::string res = "";
        for(size_t i=0;i<assertions.size();i++){
            res += "(assert " + dumpSMTLIB2(assertions[i]) + ")\n";
        }
        return res;
    }

    
    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& root, std::ofstream& ofs) {
        if (!root) return;
        
        // Record processed nodes
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        
        // Processing stack for post-order traversal
        std::stack<std::shared_ptr<DAGNode>> todo;
        
        // Record node processing status
        boost::unordered_map<std::shared_ptr<DAGNode>, bool> processed;
        
        // Initialize stack
        todo.push(root);
        
        while (!todo.empty()) {
            std::shared_ptr<DAGNode> current = todo.top();
            
            // If first visit, mark as visited
            if (visited.find(current) == visited.end()) {
                visited.insert(current);
                processed[current] = false;
            }
            
            // If all children processed, process current node
            if (processed[current]) {
                auto kind = current->getKind();
                
                switch (kind) {
                // Basic types and constants
                case NODE_KIND::NT_UNKNOWN:
                    std::cerr << "Encountered unknown node type" << std::endl;
                    assert(false);
                    break;
                case NODE_KIND::NT_ERROR:
                    std::cerr << "Encountered error node type" << std::endl;
                    assert(false);
                    break;
                case NODE_KIND::NT_NULL:
                    std::cerr << "Encountered null node type" << std::endl;
                    assert(false);
                    ofs << "NULL";
                    break;
                case NODE_KIND::NT_CONST_TRUE:
                    ofs << "true";
                    break;
                case NODE_KIND::NT_CONST_FALSE:
                    ofs << "false";
                    break;
                
                // Constants and variables
                case NODE_KIND::NT_CONST:
                    ofs << dumpConst(current->getName(), current->getSort());
                    break;
                case NODE_KIND::NT_VAR:
                    ofs << current->getName();
                    break;
                    
                // Unary operations - accept one parameter
                case NODE_KIND::NT_NOT:
                case NODE_KIND::NT_NEG:
                case NODE_KIND::NT_ABS:
                case NODE_KIND::NT_SQRT:
                case NODE_KIND::NT_CEIL:
                case NODE_KIND::NT_FLOOR:
                case NODE_KIND::NT_ROUND:
                case NODE_KIND::NT_EXP:
                case NODE_KIND::NT_LN:
                case NODE_KIND::NT_LG:
                case NODE_KIND::NT_SIN:
                case NODE_KIND::NT_COS:
                case NODE_KIND::NT_SEC:
                case NODE_KIND::NT_CSC:
                case NODE_KIND::NT_TAN:
                case NODE_KIND::NT_COT:
                case NODE_KIND::NT_ASIN:
                case NODE_KIND::NT_ACOS:
                case NODE_KIND::NT_ASEC:
                case NODE_KIND::NT_ACSC:
                case NODE_KIND::NT_ATAN:
                case NODE_KIND::NT_ACOT:
                case NODE_KIND::NT_SINH:
                case NODE_KIND::NT_COSH:
                case NODE_KIND::NT_TANH:
                case NODE_KIND::NT_SECH:
                case NODE_KIND::NT_CSCH:
                case NODE_KIND::NT_COTH:
                case NODE_KIND::NT_ASINH:
                case NODE_KIND::NT_ACOSH:
                case NODE_KIND::NT_ATANH:
                case NODE_KIND::NT_ASECH:
                case NODE_KIND::NT_ACSCH:
                case NODE_KIND::NT_ACOTH:
                case NODE_KIND::NT_TO_INT:
                case NODE_KIND::NT_TO_REAL:
                case NODE_KIND::NT_IS_INT:
                case NODE_KIND::NT_IS_PRIME:
                case NODE_KIND::NT_IS_EVEN:
                case NODE_KIND::NT_IS_ODD:
                case NODE_KIND::NT_FACT:
                case NODE_KIND::NT_BV_NOT:
                case NODE_KIND::NT_BV_NEG:
                case NODE_KIND::NT_BV_NEGO:
                case NODE_KIND::NT_FP_ABS:
                case NODE_KIND::NT_FP_NEG:
                case NODE_KIND::NT_FP_SQRT:
                case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
                case NODE_KIND::NT_FP_IS_NORMAL:
                case NODE_KIND::NT_FP_IS_SUBNORMAL:
                case NODE_KIND::NT_FP_IS_ZERO:
                case NODE_KIND::NT_FP_IS_INF:
                case NODE_KIND::NT_FP_IS_NAN:
                case NODE_KIND::NT_FP_IS_NEG:
                case NODE_KIND::NT_FP_IS_POS:
                case NODE_KIND::NT_FP_TO_UBV:
                case NODE_KIND::NT_FP_TO_SBV:
                case NODE_KIND::NT_FP_TO_REAL:
                case NODE_KIND::NT_FP_TO_FP:
                case NODE_KIND::NT_STR_LEN:
                case NODE_KIND::NT_STR_TO_LOWER:
                case NODE_KIND::NT_STR_TO_UPPER:
                case NODE_KIND::NT_STR_REV:
                case NODE_KIND::NT_STR_IS_DIGIT:
                case NODE_KIND::NT_STR_FROM_INT:
                case NODE_KIND::NT_STR_TO_INT:
                case NODE_KIND::NT_STR_TO_REG:
                case NODE_KIND::NT_STR_TO_CODE:
                case NODE_KIND::NT_STR_FROM_CODE:
                case NODE_KIND::NT_REG_STAR:
                case NODE_KIND::NT_REG_PLUS:
                case NODE_KIND::NT_REG_OPT:
                case NODE_KIND::NT_REG_COMPLEMENT:
                case NODE_KIND::NT_BV_TO_NAT:
                case NODE_KIND::NT_NAT_TO_BV:
                case NODE_KIND::NT_POW2:
                    ofs << "(" << kindToString(kind) << " ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << ")";
                    break;
                    
                // Binary operations - accept two parameters
                case NODE_KIND::NT_EQ:
                case NODE_KIND::NT_EQ_BOOL:
                case NODE_KIND::NT_EQ_OTHER:
                case NODE_KIND::NT_POW:
                case NODE_KIND::NT_DIV_INT:
                case NODE_KIND::NT_DIV_REAL:
                case NODE_KIND::NT_MOD:
                case NODE_KIND::NT_LOG:
                case NODE_KIND::NT_LE:
                case NODE_KIND::NT_LT:
                case NODE_KIND::NT_GE:
                case NODE_KIND::NT_GT:
                case NODE_KIND::NT_IS_DIVISIBLE:
                case NODE_KIND::NT_GCD:
                case NODE_KIND::NT_LCM:
                case NODE_KIND::NT_BV_UDIV:
                case NODE_KIND::NT_BV_SDIV:
                case NODE_KIND::NT_BV_UREM:
                case NODE_KIND::NT_BV_SREM:
                case NODE_KIND::NT_BV_UMOD:
                case NODE_KIND::NT_BV_SMOD:
                case NODE_KIND::NT_BV_SDIVO:
                case NODE_KIND::NT_BV_UDIVO:
                case NODE_KIND::NT_BV_SREMO:
                case NODE_KIND::NT_BV_UREMO:
                case NODE_KIND::NT_BV_SMODO:
                case NODE_KIND::NT_BV_UMODO:
                case NODE_KIND::NT_BV_SHL:
                case NODE_KIND::NT_BV_LSHR:
                case NODE_KIND::NT_BV_ASHR:
                case NODE_KIND::NT_BV_ULT:
                case NODE_KIND::NT_BV_ULE:
                case NODE_KIND::NT_BV_UGT:
                case NODE_KIND::NT_BV_UGE:
                case NODE_KIND::NT_BV_SLT:
                case NODE_KIND::NT_BV_SLE:
                case NODE_KIND::NT_BV_SGT:
                case NODE_KIND::NT_BV_SGE:
                case NODE_KIND::NT_FP_DIV:
                case NODE_KIND::NT_FP_REM:
                case NODE_KIND::NT_FP_LE:
                case NODE_KIND::NT_FP_LT:
                case NODE_KIND::NT_FP_GE:
                case NODE_KIND::NT_FP_GT:
                case NODE_KIND::NT_FP_EQ:
                case NODE_KIND::NT_SELECT:
                case NODE_KIND::NT_STR_PREFIXOF:
                case NODE_KIND::NT_STR_SUFFIXOF:
                case NODE_KIND::NT_STR_CHARAT:
                case NODE_KIND::NT_STR_SPLIT:
                case NODE_KIND::NT_STR_LT:
                case NODE_KIND::NT_STR_LE:
                case NODE_KIND::NT_STR_GT:
                case NODE_KIND::NT_STR_GE:
                case NODE_KIND::NT_STR_IN_REG:
                case NODE_KIND::NT_STR_CONTAINS:
                case NODE_KIND::NT_REG_RANGE:
                case NODE_KIND::NT_REG_REPEAT:
                    ofs << "(" << kindToString(kind) << " ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << " ";
                    dumpSMTLIB2(current->getChild(1), ofs);
                    ofs << ")";
                    break;
                    
                // Ternary operations - accept three parameters
                case NODE_KIND::NT_ITE:
                case NODE_KIND::NT_FP_FMA:
                case NODE_KIND::NT_STORE:
                case NODE_KIND::NT_STR_SUBSTR:
                case NODE_KIND::NT_STR_INDEXOF:
                case NODE_KIND::NT_STR_UPDATE:
                case NODE_KIND::NT_STR_REPLACE:
                case NODE_KIND::NT_STR_REPLACE_ALL:
                case NODE_KIND::NT_REG_LOOP:
                case NODE_KIND::NT_REPLACE_REG:
                case NODE_KIND::NT_REPLACE_REG_ALL:
                case NODE_KIND::NT_INDEXOF_REG:
                    ofs << "(" << kindToString(kind) << " ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << " ";
                    dumpSMTLIB2(current->getChild(1), ofs);
                    ofs << " ";
                    dumpSMTLIB2(current->getChild(2), ofs);
                    ofs << ")";
                    break;
                    
                // Multi-parameter operations - accept arbitrary number of parameters
                case NODE_KIND::NT_DISTINCT:
                case NODE_KIND::NT_DISTINCT_BOOL:
                case NODE_KIND::NT_DISTINCT_OTHER:
                case NODE_KIND::NT_AND:
                case NODE_KIND::NT_OR:
                case NODE_KIND::NT_IMPLIES:
                case NODE_KIND::NT_XOR:
                case NODE_KIND::NT_ADD:
                case NODE_KIND::NT_MUL:
                case NODE_KIND::NT_IAND:
                case NODE_KIND::NT_SUB:
                case NODE_KIND::NT_BV_AND:
                case NODE_KIND::NT_BV_OR:
                case NODE_KIND::NT_BV_XOR:
                case NODE_KIND::NT_BV_NAND:
                case NODE_KIND::NT_BV_NOR:
                case NODE_KIND::NT_BV_XNOR:
                case NODE_KIND::NT_BV_COMP:
                case NODE_KIND::NT_BV_ADD:
                case NODE_KIND::NT_BV_SUB:
                case NODE_KIND::NT_BV_MUL:
                case NODE_KIND::NT_BV_SADDO:
                case NODE_KIND::NT_BV_UADDO:
                case NODE_KIND::NT_BV_SMULO:
                case NODE_KIND::NT_BV_UMULO:
                case NODE_KIND::NT_BV_CONCAT:
                case NODE_KIND::NT_FP_ADD:
                case NODE_KIND::NT_FP_SUB:
                case NODE_KIND::NT_FP_MUL:
                case NODE_KIND::NT_FP_MIN:
                case NODE_KIND::NT_FP_MAX:
                case NODE_KIND::NT_STR_CONCAT:
                case NODE_KIND::NT_REG_CONCAT:
                case NODE_KIND::NT_REG_UNION:
                case NODE_KIND::NT_REG_INTER:
                case NODE_KIND::NT_REG_DIFF: {
                    ofs << "(" << kindToString(kind);
                    for (auto& child : current->getChildren()) {
                        ofs << " ";
                        dumpSMTLIB2(child, ofs);
                    }
                    ofs << ")";
                    break;
                }
                    
                // Special processing operations
                case NODE_KIND::NT_BV_EXTRACT:
                    ofs << "((_ extract ";
                    dumpSMTLIB2(current->getChild(1), ofs);
                    ofs << " ";
                    dumpSMTLIB2(current->getChild(2), ofs);
                    ofs << ") ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << ")";
                    break;
                    
                case NODE_KIND::NT_BV_REPEAT:
                case NODE_KIND::NT_BV_ZERO_EXT:
                case NODE_KIND::NT_BV_SIGN_EXT:
                case NODE_KIND::NT_BV_ROTATE_LEFT:
                case NODE_KIND::NT_BV_ROTATE_RIGHT:
                    ofs << "((_ " << kindToString(kind) << " ";
                    dumpSMTLIB2(current->getChild(1), ofs);
                    ofs << ") ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << ")";
                    break;
                    
                // Constants
                case NODE_KIND::NT_PI:
                    ofs << "pi";
                    break;
                case NODE_KIND::NT_E:
                    ofs << "e";
                    break;
                case NODE_KIND::NT_INFINITY:
                    ofs << "inf";
                    break;
                case NODE_KIND::NT_NAN:
                    ofs << "NaN";
                    break;
                case NODE_KIND::NT_EPSILON:
                    ofs << "epsilon";
                    break;
                case NODE_KIND::NT_REG_NONE:
                    ofs << "re.none";
                    break;
                case NODE_KIND::NT_REG_ALL:
                    ofs << "re.all";
                    break;
                case NODE_KIND::NT_REG_ALLCHAR:
                    ofs << "re.allchar";
                    break;
                    
                // Quantifiers
                case NODE_KIND::NT_FORALL:
                case NODE_KIND::NT_EXISTS: {
                    ofs << "(" << kindToString(kind) << " (";
                    for (size_t i = 1; i < current->getChildrenSize(); i++) {
                        if (i > 1) ofs << " ";
                        ofs << "(";
                        dumpSMTLIB2(current->getChild(i), ofs);
                        ofs << " " << current->getChild(i)->getSort()->toString() << ")";
                    }
                    ofs << ") ";
                    dumpSMTLIB2(current->getChild(0), ofs);
                    ofs << ")";
                    break;
                }
                
                case NODE_KIND::NT_QUANT_VAR:
                    ofs << current->getName();
                    break;
                    
                // Function related
                case NODE_KIND::NT_FUNC_DEC:
                case NODE_KIND::NT_FUNC_DEF:
                case NODE_KIND::NT_FUNC_PARAM:
                    ofs << current->getName();
                    break;
                    
                case NODE_KIND::NT_FUNC_APPLY: {
                    ofs << "(" << current->getName();
                    for (size_t i = 1; i < current->getChildrenSize(); i++) {
                        ofs << " ";
                        dumpSMTLIB2(current->getChild(i), ofs);
                    }
                    ofs << ")";
                    break;
                }
                
                case NODE_KIND::NT_LET:
                    dumpSMTLIB2(current->getChild(0), ofs);
                    break;
                    
                case NODE_KIND::NT_APPLY_UF:
                    ofs << "(" << current->getName();
                    for (auto& child : current->getChildren()) {
                        ofs << " ";
                        dumpSMTLIB2(child, ofs);
                    }
                    ofs << ")";
                    break;
                    
                default:
                    std::cerr << "Unknown operator type: " << static_cast<int>(kind) << std::endl;
                    ofs << "UNKNOWN_KIND";
                }
                
                todo.pop();
                continue;
            }
            
            // Check if all children need to be added
            bool allChildrenProcessed = true;
            for (auto& child : current->getChildren()) {
                if (visited.find(child) == visited.end()) {
                    allChildrenProcessed = false;
                    todo.push(child);
                }
            }
            
            if (!allChildrenProcessed) {
                // If there are unprocessed child nodes, wait for all children to be processed
                processed[current] = false;
            } else {
                // If all child nodes have been processed, mark current node as processed
                processed[current] = true;
            }
        }
    }

    void dumpSMTLIB2(const std::vector<std::shared_ptr<DAGNode>>& assertions, std::ofstream& ofs) {
        for (size_t i = 0; i < assertions.size(); i++) {
            ofs << "(assert ";
            dumpSMTLIB2(assertions[i], ofs);
            ofs << ")\n";
        }
    }

    void dumpFuncDef(const std::shared_ptr<DAGNode>& node, std::ofstream& ofs) {
        ofs << "(define-fun " << node->getName() << " (";
        for (size_t i = 1; i < node->getChildrenSize(); i++) {
            if (i > 1) ofs << " ";
            ofs << "(" << node->getChild(i)->getName() << " " << node->getChild(i)->getSort()->toString() << ")";
        }
        ofs << ") " << node->getChild(0)->getSort()->toString() << " ";
        dumpSMTLIB2(node->getChild(0), ofs);
        ofs << ")";
    }

    void dumpFuncDec(const std::shared_ptr<DAGNode>& node, std::ofstream& ofs) {
        ofs << "(declare-fun " << node->getName() << " (";
        for (size_t i = 1; i < node->getChildrenSize(); i++) {
            if (i > 1) ofs << " ";
            ofs << node->getChild(i)->getSort()->toString();
        }
        ofs << ") " << node->getChild(0)->getSort()->toString() << ")";
    }
}