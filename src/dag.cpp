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
#include <sstream>

namespace SMTParser{

    void DAGNode::updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        condAssert(out_sort == sort, "updateFuncDef: out_sort != sort");
        (void)out_sort;
        children.clear();
        children.emplace_back(body);
        for(auto& p : params){
            children.emplace_back(p);
        }
        kind = NODE_KIND::NT_FUNC_DEF;
    }

    
    void DAGNode::updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params){
        condAssert(out_sort == sort, "updateApplyFunc: out_sort != sort");
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

    // High-performance iterative streaming version to avoid stack overflow
    void dumpSMTLIB2_streaming(const std::shared_ptr<DAGNode>& root, std::ostream& out) {
        if (!root) return;

        std::shared_ptr<DAGNode> actualRoot = root;

        // Static kind string cache for performance
        static std::unordered_map<NODE_KIND, const char*> kind_cache;
        static bool cache_initialized = false;

        if (!cache_initialized) {
            kind_cache[NODE_KIND::NT_NOT] = "not";
            kind_cache[NODE_KIND::NT_AND] = "and";
            kind_cache[NODE_KIND::NT_OR] = "or";
            kind_cache[NODE_KIND::NT_ADD] = "+";
            kind_cache[NODE_KIND::NT_MUL] = "*";
            kind_cache[NODE_KIND::NT_SUB] = "-";
            kind_cache[NODE_KIND::NT_EQ] = "=";
            kind_cache[NODE_KIND::NT_LE] = "<=";
            kind_cache[NODE_KIND::NT_LT] = "<";
            kind_cache[NODE_KIND::NT_GE] = ">=";
            kind_cache[NODE_KIND::NT_GT] = ">";
            kind_cache[NODE_KIND::NT_ITE] = "ite";
            kind_cache[NODE_KIND::NT_IMPLIES] = "=>";
            kind_cache[NODE_KIND::NT_XOR] = "xor";
            kind_cache[NODE_KIND::NT_DIV_REAL] = "/";
            kind_cache[NODE_KIND::NT_NEG] = "-";
            kind_cache[NODE_KIND::NT_DISTINCT] = "distinct";
            cache_initialized = true;
        }

        // Optimized iterative implementation using minimal WorkItem structure
        struct WorkItem {
            DAGNode* node;
            uint8_t action; // 0=process, 1=space, 2=close_paren

            WorkItem(DAGNode* n, uint8_t a = 0) : node(n), action(a) {}
        };

        // Pre-allocate stack with reasonable capacity to avoid frequent reallocations
        std::vector<WorkItem> work_stack;
        work_stack.reserve(10000); // Reserve space for deep expressions
        work_stack.emplace_back(actualRoot.get(), 0);

        while (!work_stack.empty()) {
            WorkItem item = work_stack.back();
            work_stack.pop_back();

            if (item.action == 1) { // Write space
                out << " ";
                continue;
            }
            if (item.action == 2) { // Write closing paren
                out << ")";
                continue;
            }
            if (item.action == 3) { // Write ") " for special cases
                out << ") ";
                continue;
            }

            // Process node (action == 0)
            DAGNode* node = item.node;
            if (!node) continue;

            auto kind = node->getKind();
            switch (kind) {
            case NODE_KIND::NT_CONST_TRUE:
                out << "true";
                break;
            case NODE_KIND::NT_CONST_FALSE:
                out << "false";
                break;
            case NODE_KIND::NT_CONST:
                out << dumpConst(node->getName(), node->getSort());
                break;
            case NODE_KIND::NT_VAR:
            case NODE_KIND::NT_TEMP_VAR:
                out << node->getName();
                break;

            // Binary operations - optimized for common case
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_SUB:
            case NODE_KIND::NT_DIV_REAL: {
                if (node->getChildrenSize() == 2) {
                    auto child0 = node->getChild(0).get();
                    auto child1 = node->getChild(1).get();

                    const char* op = kind_cache[kind];
                    out << "(" << op << " ";

                    // Push in reverse order: close_paren, child1, space, child0
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child1, 0);   // child1
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(child0, 0);   // child0
                    break;
                }
                // Fall through to n-ary case
                [[fallthrough]];
            }
            // N-ary operations - most common case, highly optimized
            case NODE_KIND::NT_AND:
            case NODE_KIND::NT_OR:
            case NODE_KIND::NT_DISTINCT: {
                const char* op = kind_cache[kind];
                if (!op) op = kindToString(kind).c_str();

                out << "(" << op;
                const auto& children = node->getChildren();

                // Push closing paren first
                work_stack.emplace_back(nullptr, 2);

                // Push children in reverse order, each preceded by a space
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto child = children[i].get();
                    work_stack.emplace_back(child, 0);
                    work_stack.emplace_back(nullptr, 1); // space before child
                }
                break;
            }

            case NODE_KIND::NT_REG_LOOP: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "((_ re.loop ";

                // Push: ), child0, ") ", child2, " ", child1
                work_stack.emplace_back(nullptr, 2);     // )
                work_stack.emplace_back(child0, 0);      // child0
                work_stack.emplace_back(nullptr, 3);     // ") " - special case
                work_stack.emplace_back(child2, 0);      // child2
                work_stack.emplace_back(nullptr, 1);     // space
                work_stack.emplace_back(child1, 0);      // child1
                break;
            }
            // Unary operations
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_NEG: {
                auto child = node->getChild(0).get();
                const char* op = kind_cache[kind];

                out << "(" << op << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child, 0);    // child
                break;
            }

            // Ternary operations
            case NODE_KIND::NT_ITE: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "(ite ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child2, 0);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
                break;
            }

            // Special processing operations
            case NODE_KIND::NT_BV_EXTRACT: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                auto child2 = node->getChild(2).get();

                out << "((_ extract ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child0, 0);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child2, 0);   // child2
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child1, 0);   // child1
                break;
            }
            case NODE_KIND::NT_BV_REPEAT:
            case NODE_KIND::NT_BV_ZERO_EXT:
            case NODE_KIND::NT_BV_SIGN_EXT:
            case NODE_KIND::NT_BV_ROTATE_LEFT:
            case NODE_KIND::NT_BV_ROTATE_RIGHT: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();

                out << "((_ " << kindToString(kind) << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child0, 0);   // child0
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(child1, 0);   // child1
                break;
            }

            // Constants
            case NODE_KIND::NT_CONST_PI:
                out << "pi";
                break;
            case NODE_KIND::NT_CONST_E:
                out << "e";
                break;
            case NODE_KIND::NT_INFINITY:
                out << "inf";
                break;
            case NODE_KIND::NT_POS_INFINITY:
                out << "+inf";
                break;
            case NODE_KIND::NT_NEG_INFINITY:
                out << "-inf";
                break;
            case NODE_KIND::NT_NAN:
                out << "NaN";
                break;
            case NODE_KIND::NT_EPSILON:
                out << "epsilon";
                break;
            case NODE_KIND::NT_POS_EPSILON:
                out << "+epsilon";
                break;
            case NODE_KIND::NT_NEG_EPSILON:
                out << "-epsilon";
                break;
            case NODE_KIND::NT_REG_NONE:
                out << "re.none";
                break;
            case NODE_KIND::NT_REG_ALL:
                out << "re.all";
                break;
            case NODE_KIND::NT_REG_ALLCHAR:
                out << "re.allchar";
                break;

            // Quantifiers - handle inline for performance
            case NODE_KIND::NT_FORALL:
            case NODE_KIND::NT_EXISTS: {
                out << "(" << kindToString(kind) << " (";
                for (size_t i = 1; i < node->getChildrenSize(); i++) {
                    auto current_child = node->getChild(i).get();
                    if (i == 1){
                        out << "(" << current_child->getName() << " " << current_child->getSort()->toString() << ")";
                    }
                    else{
                        out << " (" << current_child->getName() << " " << current_child->getSort()->toString() << ")";
                    }
                }
                out << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                break;
            }

            case NODE_KIND::NT_QUANT_VAR:
                out << node->getName();
                break;

            // Function related
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
            case NODE_KIND::NT_FUNC_PARAM:
                out << node->getName();
                break;

            // Function applications
            case NODE_KIND::NT_FUNC_APPLY: {
                out << "(" << node->getName();
                work_stack.emplace_back(nullptr, 2);  // )
                for (int i = node->getChildrenSize() - 1; i >= 1; i--) {
                    auto current_child = node->getChild(i).get();
                    work_stack.emplace_back(current_child, 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }

            case NODE_KIND::NT_LET: {
                condAssert(node->getChildrenSize() > 0, "NT_LET should have at least one child");
                if(node->getChildrenSize() == 1){
                    work_stack.emplace_back(node->getChild(0).get(), 0);
                }
                else{
                    if(node->getChild(1)->getKind() == NODE_KIND::NT_LET_BIND_VAR){
                        // preserved let
                        out << "(let (";  // add (
                        for(size_t i=1;i<node->getChildrenSize();i++){
                            if (i > 1) out << " ";  // add space for multiple bindings
                            out << "(" << node->getChild(i)->getPureName() << " ";
                            auto child_0 = node->getChild(i)->getChild(0);
                            out << dumpSMTLIB2(child_0);
                            work_stack.emplace_back(nullptr, 2);  // close each binding's right parenthesis
                        }
                        out << ") ";  // close binding list and add space
                        
                        // add body and final right parenthesis
                        work_stack.emplace_back(nullptr, 2);  // the right parenthesis of the whole let expression
                        work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                    }
                    else{
                        // expanded let
                        work_stack.emplace_back(node->getChild(0).get(), 0);
                    }
                }
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR: {
                out << node->getPureName();
                break;
            }

            case NODE_KIND::NT_APPLY_UF: {
                out << "(" << node->getName();
                work_stack.emplace_back(nullptr, 2);  // )
                const auto& children = node->getChildren();
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto current_child = children[i].get();
                    work_stack.emplace_back(current_child, 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }

            default: {
                // Fallback for other cases - iterative version
                std::string kind_str = kindToString(kind);
                const auto& children = node->getChildren();

                if (children.empty()) {
                    out << kind_str;
                } else if (children.size() == 1) {
                    auto child = children[0].get();
                    out << "(" << kind_str << " ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(child, 0);    // child
                } else {
                    out << "(" << kind_str;
                    work_stack.emplace_back(nullptr, 2);  // )
                    for (int i = children.size() - 1; i >= 0; i--) {
                        auto child = children[i].get();
                        work_stack.emplace_back(child, 0);
                        work_stack.emplace_back(nullptr, 1);  // space
                    }
                }
                break;
            }
            }
        }
    }

    // Wrapper function that returns string for compatibility
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& root) {
        std::ostringstream oss;
        dumpSMTLIB2_streaming(root, oss);
        return oss.str();
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
    void dumpSingleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& p, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(p, visited, ofs);
        ofs << ")";
    }

    void dumpDoubleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& r, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(l, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(r, visited, ofs);
        ofs << ")";
    }

    void dumpTripleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& m, const std::shared_ptr<DAGNode>& r, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind) + " ";
        dumpSMTLIB2(l, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(m, visited, ofs);
        ofs << " ";
        dumpSMTLIB2(r, visited, ofs);
        ofs << ")";
    }

    void dumpChainOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
        ofs << "(" + kindToString(kind);
        for (auto& node : p){
            ofs << " ";
            dumpSMTLIB2(node, visited, ofs);
        }
        ofs << ")";
    }

    void dumpQuantOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
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

    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& node, std::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs){
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
            condAssert(false, "Encountered unknown kind node");
            break;
        case NODE_KIND::NT_ERROR:
            std::cout<<"Error kind"<<std::endl;
            condAssert(false, "Encountered error kind node");
            break;
        case NODE_KIND::NT_NULL:
            std::cout<<"Null kind"<<std::endl;
            condAssert(false, "Encountered null kind node");
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
            ofs << "(" << node->getName();
            for (auto& child : node->getChildren()) {
                ofs << " ";
                dumpSMTLIB2(child, visited, ofs);
            }
            ofs << ")";
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
        case NODE_KIND::NT_POS_INFINITY:
            ofs << "+inf";
            break;
        case NODE_KIND::NT_NEG_INFINITY:
            ofs << "-inf";
            break;
        case NODE_KIND::NT_NAN:
            ofs << "NaN";
            break;
        case NODE_KIND::NT_EPSILON:
            ofs << "epsilon";
            break;
        case NODE_KIND::NT_POS_EPSILON:
            ofs << "+epsilon";
            break;
        case NODE_KIND::NT_NEG_EPSILON:
            ofs << "-epsilon";
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
        case NODE_KIND::NT_STR_SPLIT_AT:
        case NODE_KIND::NT_STR_SPLIT_REST:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        case NODE_KIND::NT_STR_TO_LOWER:
        case NODE_KIND::NT_STR_TO_UPPER:
        case NODE_KIND::NT_STR_REV:
            dumpSingleOp(kind, node->getChild(0), visited, ofs);
            break;
        case NODE_KIND::NT_STR_SPLIT:
        case NODE_KIND::NT_STR_NUM_SPLITS:
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
        // INTERVAL
        case NODE_KIND::NT_MAX:
        case NODE_KIND::NT_MIN:
            dumpChainOp(kind, node->getChildren(), visited, ofs);
            break;
        // STRINGS RE FUNCTIONS
        case NODE_KIND::NT_REPLACE_REG:
        case NODE_KIND::NT_REPLACE_REG_ALL:
        case NODE_KIND::NT_INDEXOF_REG:
            dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited, ofs);
            break;
        // LET, FROM HERE TODO
        case NODE_KIND::NT_LET:
            condAssert(node->getChildrenSize() > 0, "NT_LET should have at least one child");
            if(node->getChildrenSize() == 1){
                dumpSMTLIB2(node->getChild(0), visited, ofs);
            }
            else{
                if(node->getChild(1)->getKind() == NODE_KIND::NT_LET_BIND_VAR){
                    // preserved let
                    ofs << "(let (";
                    for(size_t i=1;i<node->getChildrenSize();i++){
                        if (i > 1) ofs << " ";  // add space for multiple bindings
                        ofs << "(" << node->getChild(i)->getPureName() << " ";
                        dumpSMTLIB2(node->getChild(i)->getChild(0), visited, ofs);
                        ofs << ")";  // close each binding's right parenthesis
                    }
                    ofs << ") ";  // close binding list
                    dumpSMTLIB2(node->getChild(0), visited, ofs);  // output body
                    ofs << ")";  // close the whole let expression
                }else{
                    // expanded let
                    dumpSMTLIB2(node->getChild(0), visited, ofs);
                }
            }
            break;
        case NODE_KIND::NT_LET_BIND_VAR:
            ofs << node->getPureName();
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
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
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
