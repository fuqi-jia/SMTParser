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

#include "dag.h"
#include <stack>

namespace SMTLIBParser{

    void DAGNode::updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        cassert(out_sort == sort, "updateFuncDef: out_sort != sort");
        (void)out_sort;
        children.clear();
        children.emplace_back(body);
        for(auto& p : params){
            children.emplace_back(p);
        }
        kind = NODE_KIND::NT_FUNC_DEF;
    }

    
    void DAGNode::updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        cassert(out_sort == sort, "updateApplyFunc: out_sort != sort");
        (void)out_sort;
        children.clear();
        children.emplace_back(body);
        for(auto& p : params){
            children.emplace_back(p);
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
        else if(sort->isInt() || sort->isIntOrReal()){
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

        bool is_let = root->isLet();
        std::shared_ptr<DAGNode> let_body = nullptr;
        if(is_let){
            let_body = root->getLetBody();
        }
        
        while (!todo.empty()) {
            // if the let body has been processed, break
            if(is_let && results.find(let_body) != results.end()){break;}

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
                    std::cerr << "Unknown kind: " << kindToString(kind) << std::endl;
                    cassert(false, "Encountered unknown kind node");
                    break;
                case NODE_KIND::NT_ERROR:
                    std::cerr << "Encountered error kind node" << std::endl;
                    cassert(false, "Encountered error kind node");
                    break;
                case NODE_KIND::NT_NULL:
                    std::cerr << "Encountered null kind node" << std::endl;
                    cassert(false, "Encountered null kind node");
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
                case NODE_KIND::NT_TEMP_VAR:
                    res = current->getName();
                    break;
                    
                // Unary operation - accepts one parameter
                case NODE_KIND::NT_NOT:
                case NODE_KIND::NT_NEG:
                case NODE_KIND::NT_ABS:
                case NODE_KIND::NT_SQRT:
                case NODE_KIND::NT_SAFESQRT:
                case NODE_KIND::NT_CEIL:
                case NODE_KIND::NT_FLOOR:
                case NODE_KIND::NT_ROUND:
                case NODE_KIND::NT_EXP:
                case NODE_KIND::NT_LN:
                case NODE_KIND::NT_LG:
                case NODE_KIND::NT_LB:
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
                case NODE_KIND::NT_BV_TO_INT:
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
                case NODE_KIND::NT_ATAN2:
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
                case NODE_KIND::NT_BV_COMP:
                case NODE_KIND::NT_BV_ULT:
                case NODE_KIND::NT_BV_ULE:
                case NODE_KIND::NT_BV_UGT:
                case NODE_KIND::NT_BV_UGE:
                case NODE_KIND::NT_BV_SLT:
                case NODE_KIND::NT_BV_SLE:
                case NODE_KIND::NT_BV_SGT:
                case NODE_KIND::NT_BV_SGE:
                case NODE_KIND::NT_NAT_TO_BV:
                case NODE_KIND::NT_INT_TO_BV:
                case NODE_KIND::NT_FP_DIV:
                case NODE_KIND::NT_FP_REM:
                case NODE_KIND::NT_FP_LE:
                case NODE_KIND::NT_FP_LT:
                case NODE_KIND::NT_FP_GE:
                case NODE_KIND::NT_FP_GT:
                case NODE_KIND::NT_FP_EQ:
                case NODE_KIND::NT_FP_NE:
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
                case NODE_KIND::NT_REPLACE_REG:
                case NODE_KIND::NT_REPLACE_REG_ALL:
                case NODE_KIND::NT_INDEXOF_REG:
                    res = "(" + kindToString(kind) + " " + results[current->getChild(0)] + " " + results[current->getChild(1)] + " " + results[current->getChild(2)] + ")";
                    break;
                case NODE_KIND::NT_REG_LOOP:
                    res = "((_ re.loop " + results[current->getChild(1)] + " " + results[current->getChild(2)] + ") " + results[current->getChild(0)] + ")";
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
                case NODE_KIND::NT_CONST_PI:
                    res = "pi";
                    break;
                case NODE_KIND::NT_CONST_E:
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
                    std::cerr << "Unknown kind: " << kindToString(kind) << std::endl;
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
        if(is_let){
            return results[let_body];
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

    // dump the node to the ofstream
    void dumpSingleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& p, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(p, visited, ofs);
        ofs << ")";
    }

    void dumpDoubleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& r, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(l, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(r, visited, ofs);
        ofs << ")";
    }

    void dumpTripleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& m, const std::shared_ptr<DAGNode>& r, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(l, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(m, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(r, visited, ofs);
        ofs << ")";
    }

    void dumpChainOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind);
        for (auto& node : p){
            ofs << " ";
            dumpSMTLIB2(node, visited, ofs);
        }
        ofs << ")";
    }

    void dumpQuantOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " (";
        for(size_t i=1;i<p.size();i++){
            if(i==1){
                ofs << "(";
                dumpSMTLIB2(p[i], visited, ofs);
                ofs << " " + p[i]->getSort()->toString() + ")";
            } 
            else {
                ofs << " (";
                dumpSMTLIB2(p[i], visited, ofs);
                ofs << " " + p[i]->getSort()->toString() + ")";
            }
        }
        ofs << ") ";
        dumpSMTLIB2(p[0], visited, ofs);
        ofs << ")";
    }

    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& node, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        if(visited.find(node) != visited.end()){
            ofs << dumpSMTLIB2(node);
            return;
        }
        visited.insert(node);
        // switch on the kind of the node
        auto kind = node->getKind();
        switch (kind)
        {
        case NODE_KIND::NT_UNKNOWN:
            std::cout<<"Unknown kind"<<std::endl;
            cassert(false, "Encountered unknown kind node");
            break;
        case NODE_KIND::NT_ERROR:
            std::cout<<"Error kind"<<std::endl;
            cassert(false, "Encountered error kind node");
            break;
        case NODE_KIND::NT_NULL:
            std::cout<<"Null kind"<<std::endl;
            cassert(false, "Encountered null kind node");
            ofs << "NULL";
            break;
        case NODE_KIND::NT_CONST_TRUE:
            ofs << "true";
            break;
        case NODE_KIND::NT_CONST_FALSE:
            ofs << "false";
            break;
        // CORE OPERATORS
        case NODE_KIND::NT_EQ:
        case NODE_KIND::NT_EQ_BOOL:
        case NODE_KIND::NT_EQ_OTHER:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_DISTINCT:
        case NODE_KIND::NT_DISTINCT_BOOL:
        case NODE_KIND::NT_DISTINCT_OTHER:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        // CONSTANT / VARIABLE
        case NODE_KIND::NT_CONST:
            ofs << dumpConst(node->getName(), node->getSort());
            break;
        case NODE_KIND::NT_VAR:
            ofs << node->getName();
            break;
        // BOOLEAN
        case NODE_KIND::NT_NOT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_AND:
        case NODE_KIND::NT_OR:
        case NODE_KIND::NT_IMPLIES:
        case NODE_KIND::NT_XOR:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        // UF
        case NODE_KIND::NT_APPLY_UF:
            ofs << "APPLY_UF";
            break;
        // ARITHMATIC COMMON OPERATORS
        case NODE_KIND::NT_ADD:
        case NODE_KIND::NT_MUL:
        case NODE_KIND::NT_IAND:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_POW2:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_POW:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_SUB:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_NEG:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_DIV_INT:
        case NODE_KIND::NT_DIV_REAL:
        case NODE_KIND::NT_MOD:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_ABS:
        case NODE_KIND::NT_SQRT:
        case NODE_KIND::NT_SAFESQRT:
        case NODE_KIND::NT_CEIL:
        case NODE_KIND::NT_FLOOR:
        case NODE_KIND::NT_ROUND:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // TRANSCENDENTAL ARITHMATIC
        case NODE_KIND::NT_EXP:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_LOG:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_LN:
        case NODE_KIND::NT_LG:
        case NODE_KIND::NT_LB:
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
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_ATAN2:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_LE:
        case NODE_KIND::NT_LT:
        case NODE_KIND::NT_GE:
        case NODE_KIND::NT_GT:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // ARITHMATIC CONVERSION
        case NODE_KIND::NT_TO_INT:
        case NODE_KIND::NT_TO_REAL:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // ARITHMATIC PROPERTIES
        case NODE_KIND::NT_IS_INT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_IS_DIVISIBLE:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_IS_PRIME:
        case NODE_KIND::NT_IS_EVEN:
        case NODE_KIND::NT_IS_ODD:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // ARITHMATIC CONSTANTS
        case NODE_KIND::NT_CONST_PI:
            ofs << "pi";
            break;
        case NODE_KIND::NT_CONST_E:
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
        case NODE_KIND::NT_GCD:
        case NODE_KIND::NT_LCM:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_FACT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // BITVECTOR COMMON OPERATORS
        // Bit-wise operations
        case NODE_KIND::NT_BV_NOT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_BV_AND:
        case NODE_KIND::NT_BV_OR:
        case NODE_KIND::NT_BV_XOR:
        case NODE_KIND::NT_BV_NAND:
        case NODE_KIND::NT_BV_NOR:
        case NODE_KIND::NT_BV_XNOR:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        // Arithmetic operations
        case NODE_KIND::NT_BV_NEG:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_BV_ADD:
        case NODE_KIND::NT_BV_SUB:
        case NODE_KIND::NT_BV_MUL:
        case NODE_KIND::NT_BV_COMP:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_BV_UDIV:
        case NODE_KIND::NT_BV_SDIV:
        case NODE_KIND::NT_BV_UREM:
        case NODE_KIND::NT_BV_SREM:
        case NODE_KIND::NT_BV_UMOD:
        case NODE_KIND::NT_BV_SMOD:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // Arithmetic operations with overflow
        case NODE_KIND::NT_BV_NEGO:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_BV_SADDO:
        case NODE_KIND::NT_BV_UADDO:
        case NODE_KIND::NT_BV_SMULO:
        case NODE_KIND::NT_BV_UMULO:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_BV_SDIVO:
        case NODE_KIND::NT_BV_UDIVO:
        case NODE_KIND::NT_BV_SREMO:
        case NODE_KIND::NT_BV_UREMO:
        case NODE_KIND::NT_BV_SMODO:
        case NODE_KIND::NT_BV_UMODO:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // Shift operations
        case NODE_KIND::NT_BV_SHL:
        case NODE_KIND::NT_BV_LSHR:
        case NODE_KIND::NT_BV_ASHR:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // Function
        case NODE_KIND::NT_BV_CONCAT:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_BV_EXTRACT:
            ofs << "((_ extract ";
            dumpSMTLIB2(node->getChild(1), visited, ofs);
            ofs << " ";
            dumpSMTLIB2(node->getChild(2), visited, ofs);
            ofs << ") ";
            dumpSMTLIB2(node->getChild(0), visited, ofs);
            ofs << ")";
            break;
        case NODE_KIND::NT_BV_REPEAT:
        case NODE_KIND::NT_BV_ZERO_EXT:
        case NODE_KIND::NT_BV_SIGN_EXT:
        case NODE_KIND::NT_BV_ROTATE_LEFT:
        case NODE_KIND::NT_BV_ROTATE_RIGHT:
            ofs << "((_ " + kindToString(kind) + " ";
            dumpSMTLIB2(node->getChild(1), visited, ofs);
            ofs << ") ";
            dumpSMTLIB2(node->getChild(0), visited, ofs);
            ofs << ")";
            break;
        // BITVECTOR COMP
        case NODE_KIND::NT_BV_ULT:
        case NODE_KIND::NT_BV_ULE:
        case NODE_KIND::NT_BV_UGT:
        case NODE_KIND::NT_BV_UGE:
        case NODE_KIND::NT_BV_SLT:
        case NODE_KIND::NT_BV_SLE:
        case NODE_KIND::NT_BV_SGT:
        case NODE_KIND::NT_BV_SGE:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // BITVECTOR CONVERSION
        case NODE_KIND::NT_BV_TO_NAT:
        case NODE_KIND::NT_NAT_TO_BV:
        case NODE_KIND::NT_BV_TO_INT:
        case NODE_KIND::NT_INT_TO_BV:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // FLOATING POINT COMMON OPERATORS
        case NODE_KIND::NT_FP_ADD:
        case NODE_KIND::NT_FP_SUB:
        case NODE_KIND::NT_FP_MUL:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_FP_DIV:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_FP_ABS:
        case NODE_KIND::NT_FP_NEG:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_FP_REM:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_FP_FMA:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        case NODE_KIND::NT_FP_SQRT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_FP_MIN:
        case NODE_KIND::NT_FP_MAX:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        // FLOATING POINT COMP
        case NODE_KIND::NT_FP_LE:
        case NODE_KIND::NT_FP_LT:
        case NODE_KIND::NT_FP_GE:
        case NODE_KIND::NT_FP_GT:
        case NODE_KIND::NT_FP_EQ:
        case NODE_KIND::NT_FP_NE:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // FLOATING POINT CONVERSION
        case NODE_KIND::NT_FP_TO_UBV:
        case NODE_KIND::NT_FP_TO_SBV:
        case NODE_KIND::NT_FP_TO_REAL:
        case NODE_KIND::NT_FP_TO_FP:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // FLOATING POINT PROPERTIES
        case NODE_KIND::NT_FP_IS_NORMAL:
        case NODE_KIND::NT_FP_IS_SUBNORMAL:
        case NODE_KIND::NT_FP_IS_ZERO:
        case NODE_KIND::NT_FP_IS_INF:
        case NODE_KIND::NT_FP_IS_NAN:
        case NODE_KIND::NT_FP_IS_NEG:
        case NODE_KIND::NT_FP_IS_POS:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // ARRAY
        case NODE_KIND::NT_SELECT:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_STORE:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        // STRINGS COMMON OPERATORS
        case NODE_KIND::NT_STR_LEN:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_STR_CONCAT:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_STR_SUBSTR:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        case NODE_KIND::NT_STR_PREFIXOF:
        case NODE_KIND::NT_STR_SUFFIXOF:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_STR_INDEXOF:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        case NODE_KIND::NT_STR_CHARAT: 
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_STR_UPDATE:
        case NODE_KIND::NT_STR_REPLACE:
        case NODE_KIND::NT_STR_REPLACE_ALL:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        case NODE_KIND::NT_STR_TO_LOWER:
        case NODE_KIND::NT_STR_TO_UPPER:
        case NODE_KIND::NT_STR_REV:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_STR_SPLIT:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // STRINGS COMP
        case NODE_KIND::NT_STR_LT:
        case NODE_KIND::NT_STR_LE:
        case NODE_KIND::NT_STR_GT:
        case NODE_KIND::NT_STR_GE:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        // STRINGS PROPERTIES
        case NODE_KIND::NT_STR_IN_REG:
        case NODE_KIND::NT_STR_CONTAINS:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_STR_IS_DIGIT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // STRINGS CONVERSION
        case NODE_KIND::NT_STR_FROM_INT:
        case NODE_KIND::NT_STR_TO_INT:
        case NODE_KIND::NT_STR_TO_REG:
        case NODE_KIND::NT_STR_TO_CODE:
        case NODE_KIND::NT_STR_FROM_CODE:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
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
        case NODE_KIND::NT_REG_CONCAT:
        case NODE_KIND::NT_REG_UNION:
        case NODE_KIND::NT_REG_INTER:
        case NODE_KIND::NT_REG_DIFF:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_REG_STAR:
        case NODE_KIND::NT_REG_PLUS:
        case NODE_KIND::NT_REG_OPT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_REG_RANGE:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_REG_REPEAT:
            dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited, ofs);
            break;
        case NODE_KIND::NT_REG_LOOP:
            ofs << "((_ re.loop ";
            dumpSMTLIB2(node->getChild(1), visited, ofs);
            ofs << " ";
            dumpSMTLIB2(node->getChild(2), visited, ofs);
            ofs << ") ";
            dumpSMTLIB2(node->getChild(0), visited, ofs);
            ofs << ")";
            break;
        case NODE_KIND::NT_REG_COMPLEMENT:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        // STRINGS RE FUNCTIONS
        case NODE_KIND::NT_REPLACE_REG:
        case NODE_KIND::NT_REPLACE_REG_ALL:
        case NODE_KIND::NT_INDEXOF_REG:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        // LET, FROM HERE TODO
        case NODE_KIND::NT_LET:
            dumpSMTLIB2(node->getChild(0), visited, ofs);
            break;
        // ITE
        case NODE_KIND::NT_ITE:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        // QUANTIFIERS
        case NODE_KIND::NT_FORALL:
        case NODE_KIND::NT_EXISTS:
            dumpQuantOp(kind, node->getChildren(), visited, ofs);
            break;
        case NODE_KIND::NT_QUANT_VAR:
            ofs << node->getName();
            break;
        // FUNC
        case NODE_KIND::NT_FUNC_DEC:
            ofs << node->getName();
            break;
        case NODE_KIND::NT_FUNC_DEF:
            ofs << node->getName();
            break;
        case NODE_KIND::NT_FUNC_PARAM:
            ofs << node->getName();
            break;
        case NODE_KIND::NT_FUNC_APPLY:{
            ofs << "(" + node->getName();
            for(size_t i=1;i<node->getChildrenSize();i++){
                ofs << " ";
                dumpSMTLIB2(node->getChild(i), visited, ofs);
            }
            ofs << ")";
            break;
        }
        default:
            ofs << "UNKNOWN_KIND";
        }
    }
    
    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& root, std::ofstream& ofs) {
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        dumpSMTLIB2(root, visited, ofs);
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
        ofs << ")\n";
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