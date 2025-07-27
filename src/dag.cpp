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
#include "timing.h"
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
        else if(sort->isBool()){
            return name;
        }
        else if(sort->isBv()){
            return name;
        }
        else if(sort->isFp()){
            return name;
        }
        else if(sort->isStr()){
            return name;
        }
        else if(sort->isArray()){
            return name;
        }
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
            kind_cache[NODE_KIND::NT_FP_ADD] = "fp.add";
            kind_cache[NODE_KIND::NT_FP_SUB] = "fp.sub";
            kind_cache[NODE_KIND::NT_FP_MUL] = "fp.mul";
            kind_cache[NODE_KIND::NT_FP_DIV] = "fp.div";
            kind_cache[NODE_KIND::NT_FP_ABS] = "fp.abs";
            kind_cache[NODE_KIND::NT_FP_NEG] = "fp.neg";
            kind_cache[NODE_KIND::NT_FP_SQRT] = "fp.sqrt";
            kind_cache[NODE_KIND::NT_FP_LE] = "fp.le";
            kind_cache[NODE_KIND::NT_FP_LT] = "fp.lt";
            kind_cache[NODE_KIND::NT_FP_GE] = "fp.ge";
            kind_cache[NODE_KIND::NT_FP_GT] = "fp.gt";
            kind_cache[NODE_KIND::NT_FP_EQ] = "fp.eq";
            kind_cache[NODE_KIND::NT_FP_NE] = "fp.ne";
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
        work_stack.reserve(65536); // Reserve space for deep expressions
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
                out << "(let (";  // add (
                for(size_t i=1;i<node->getChildrenSize();i++){
                    if (i > 1) out << " ";  // add space for multiple bindings
                    out << "(" << node->getChild(i)->getPureName() << " ";
                    auto child_0 = node->getChild(i)->getChild(0).get();
                    work_stack.emplace_back(child_0, 0);
                    work_stack.emplace_back(nullptr, 2);  // close each binding's right parenthesis
                }
                out << ") ";  // close binding list and add space
                
                // add body and final right parenthesis
                work_stack.emplace_back(nullptr, 2);  // the right parenthesis of the whole let expression
                work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                break;
            }
            case NODE_KIND::NT_LET_CHAIN: {
                // let-chain:
                // children: [LET_BIND_VAR_LIST, LET_BIND_VAR_LIST, ..., Body]
                // output the let-binding list
                for(size_t i=0;i<node->getChildrenSize();i++){
                    if(i < node->getChildrenSize() - 1){ // LET_BIND_VAR_LIST
                        condAssert(node->getChild(i)->isLetBindVarList(), "NT_LET_CHAIN: child is not LET_BIND_VAR_LIST");
                        auto var_list = node->getChild(i);
                        // output let + binding list
                        out << "(let (";
                        for(size_t j=0;j<var_list->getChildrenSize();j++){
                            if(j==0) out << "(" << var_list->getChild(j)->getPureName() << " ";
                            else out << " (" << var_list->getChild(j)->getPureName() << " ";
                            auto child_0 = var_list->getChild(j)->getChild(0).get();
                            work_stack.emplace_back(child_0, 0);
                            out << ")"; // close each binding's right parenthesis and add space
                        }
                        out << ") ";
                    }
                    else{ // Body
                        work_stack.emplace_back(node->getChild(i).get(), 0);
                    }
                }
                for(size_t i=0;i<node->getChildrenSize() - 1;i++){
                    out << ")";
                }
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR: {
                out << node->getPureName();
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR_LIST: {
                out <<"( ";
                for(size_t i=1;i<node->getChildrenSize();i++){
                    if(i==1) out << "(" << node->getChild(i)->getPureName() << " ";
                    else out << " (" << node->getChild(i)->getPureName() << " ";
                    auto child_0 = node->getChild(i)->getChild(0).get();
                    work_stack.emplace_back(child_0, 0);
                    out << ")"; // close each binding's right parenthesis
                }
                out << ")";
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

            // FLOATING POINT OPERATIONS
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_DIV:
            case NODE_KIND::NT_FP_FMA:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX: {
                std::string kind_str = kindToString(kind);
                out << "(" << kind_str;
                work_stack.emplace_back(nullptr, 2);  // )
                const auto& children = node->getChildren();
                for (int i = children.size() - 1; i >= 0; i--) {
                    auto current_child = children[i].get();
                    work_stack.emplace_back(current_child, 0);
                    work_stack.emplace_back(nullptr, 1);  // space
                }
                break;
            }

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
            case NODE_KIND::NT_FP_TO_REAL: {
                std::string kind_str = kindToString(kind);
                auto child = node->getChild(0).get();
                out << "(" << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child, 0);    // child
                break;
            }

            case NODE_KIND::NT_FP_REM: {
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                out << "(fp.rem ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
                break;
            }

            case NODE_KIND::NT_FP_LE:
            case NODE_KIND::NT_FP_LT:
            case NODE_KIND::NT_FP_GE:
            case NODE_KIND::NT_FP_GT:
            case NODE_KIND::NT_FP_EQ:
            case NODE_KIND::NT_FP_NE: {
                std::string kind_str = kindToString(kind);
                auto child0 = node->getChild(0).get();
                auto child1 = node->getChild(1).get();
                out << "(" << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(child1, 0);   // child1
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(child0, 0);   // child0
                break;
            }

            case NODE_KIND::NT_FP_TO_UBV:
            case NODE_KIND::NT_FP_TO_SBV: {
                std::string kind_str = kindToString(kind);
                auto rm = node->getChild(0).get();
                auto fp = node->getChild(1).get();
                auto size = node->getChild(2).get();
                out << "(" << kind_str << " ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(size, 0);     // size
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(fp, 0);       // fp
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0);       // rm
                break;
            }

            case NODE_KIND::NT_FP_TO_FP: {
                auto eb = node->getChild(0).get();
                auto sb = node->getChild(1).get();
                auto rm = node->getChild(2).get();
                auto param = node->getChild(3).get();
                out << "((_ to_fp ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(param, 0);    // param
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(sb, 0);       // sb
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(eb, 0);       // eb
                break;
            }

            case NODE_KIND::NT_FP_TO_FP_UNSIGNED: {
                auto eb = node->getChild(0).get();
                auto sb = node->getChild(1).get();
                auto rm = node->getChild(2).get();
                auto param = node->getChild(3).get();
                out << "((_ to_fp_unsigned ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(param, 0);    // param
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(rm, 0);       // rm
                work_stack.emplace_back(nullptr, 3);  // ") "
                work_stack.emplace_back(sb, 0);       // sb
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(eb, 0);       // eb
                break;
            }

            case NODE_KIND::NT_FP_CONST: {
                auto sign = node->getChild(0).get();
                auto exp = node->getChild(1).get();
                auto mant = node->getChild(2).get();
                out << "(fp ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(mant, 0);     // mant
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(exp, 0);      // exp
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(sign, 0);     // sign
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

    // NodeManager
    
    // Static constant node definitions
    const std::shared_ptr<DAGNode> NodeManager::NULL_NODE = std::make_shared<DAGNode>(NULL_SORT, NODE_KIND::NT_NULL, "null");
    const std::shared_ptr<DAGNode> NodeManager::UNKNOWN_NODE = std::make_shared<DAGNode>(UNKNOWN_SORT, NODE_KIND::NT_UNKNOWN, "unknown");
    const std::shared_ptr<DAGNode> NodeManager::TRUE_NODE = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_TRUE, "true");
    const std::shared_ptr<DAGNode> NodeManager::FALSE_NODE = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_FALSE, "false");
    const std::shared_ptr<DAGNode> NodeManager::E_NODE = std::make_shared<DAGNode>(REAL_SORT, NODE_KIND::NT_CONST_E, "e");
    const std::shared_ptr<DAGNode> NodeManager::PI_NODE = std::make_shared<DAGNode>(REAL_SORT, NODE_KIND::NT_CONST_PI, "pi");
    // const std::shared_ptr<DAGNode> NodeManager::INF_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_INFINITY, "INF");
    // const std::shared_ptr<DAGNode> NodeManager::POS_INF_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_POS_INFINITY, "+INF");
    // const std::shared_ptr<DAGNode> NodeManager::NEG_INF_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_NEG_INFINITY, "-INF");
    const std::shared_ptr<DAGNode> NodeManager::NAN_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_NAN, "NaN");
    const std::shared_ptr<DAGNode> NodeManager::EPSILON_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_EPSILON, "EPSILON");
    const std::shared_ptr<DAGNode> NodeManager::POS_EPSILON_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_POS_EPSILON, "+EPSILON");
    const std::shared_ptr<DAGNode> NodeManager::NEG_EPSILON_NODE = std::make_shared<DAGNode>(EXT_SORT, NODE_KIND::NT_NEG_EPSILON, "-EPSILON");
    
    // infinity
    const std::shared_ptr<DAGNode> NodeManager::STR_INF_NODE = std::make_shared<DAGNode>(STR_SORT, NODE_KIND::NT_INFINITY, "INF");
    const std::shared_ptr<DAGNode> NodeManager::STR_POS_INF_NODE = std::make_shared<DAGNode>(STR_SORT, NODE_KIND::NT_POS_INFINITY, "+INF");
    const std::shared_ptr<DAGNode> NodeManager::STR_NEG_INF_NODE = std::make_shared<DAGNode>(STR_SORT, NODE_KIND::NT_NEG_INFINITY, "-INF");
    const std::shared_ptr<DAGNode> NodeManager::INT_INF_NODE = std::make_shared<DAGNode>(INT_SORT, NODE_KIND::NT_INFINITY, "INF");
    const std::shared_ptr<DAGNode> NodeManager::INT_POS_INF_NODE = std::make_shared<DAGNode>(INT_SORT, NODE_KIND::NT_POS_INFINITY, "+INF");
    const std::shared_ptr<DAGNode> NodeManager::INT_NEG_INF_NODE = std::make_shared<DAGNode>(INT_SORT, NODE_KIND::NT_NEG_INFINITY, "-INF");
    const std::shared_ptr<DAGNode> NodeManager::REAL_INF_NODE = std::make_shared<DAGNode>(REAL_SORT, NODE_KIND::NT_INFINITY, "INF");
    const std::shared_ptr<DAGNode> NodeManager::REAL_POS_INF_NODE = std::make_shared<DAGNode>(REAL_SORT, NODE_KIND::NT_POS_INFINITY, "+INF");
    const std::shared_ptr<DAGNode> NodeManager::REAL_NEG_INF_NODE = std::make_shared<DAGNode>(REAL_SORT, NODE_KIND::NT_NEG_INFINITY, "-INF");

    NodeManager::NodeManager() {
        // 1. Reserve before inserting anything
        nodes.reserve(65536);
        for (size_t i = 0; i < NUM_KINDS; i++) {
            NODE_KIND kind = static_cast<NODE_KIND>(i);
            if (static_kinds.count(kind) > 0) {
                node_buckets[i].reserve(1);
            }
            else{
                node_buckets[i].reserve(8192);
            }
        }
        // 2. Initialize static constant nodes and insert them into buckets
        initializeStaticNodes();
    }

    NodeManager::~NodeManager(){
        clear();
    }

    std::shared_ptr<DAGNode> NodeManager::getNode(const size_t index) const{
        return nodes[index];
    }
    size_t NodeManager::getIndex(const std::shared_ptr<DAGNode>& node) const{
        auto bucket_index = static_cast<size_t>(node->getKind());
        auto& kind_bucket = node_buckets[bucket_index];
        size_t node_hash = node->hashCode();
        
        auto hash_it = kind_bucket.find(node_hash);
        if(hash_it != kind_bucket.end()) {
            for(const auto& pair : hash_it->second) {
                if(pair.first.get() == node.get() ||
                   pair.first->isEquivalentTo(*node)) {
                    return pair.second;
                }
            }
        }
        return -1;
    }
    size_t NodeManager::size() const{
        return nodes.size();
    }

    void NodeManager::clear() {
        for (auto& node : nodes) {
            node->clear();
        }
        nodes.clear();
        for (auto& bucket : node_buckets) {
            bucket.clear();
        }
    }
    
    std::shared_ptr<DAGNode> NodeManager::insertNodeToBucket(const std::shared_ptr<DAGNode>& node) {
        TIME_FUNC();
        auto bucket_index = static_cast<size_t>(node->getKind());
        auto& kind_bucket = node_buckets[bucket_index];
        
        // pre-calculate hash code to avoid repeated calculation
        size_t node_hash = node->hashCode();
        
        // secondary hash lookup: first use hash code to locate the small bucket
        auto hash_it = kind_bucket.find(node_hash);
        if(hash_it != kind_bucket.end()) {
            TIME_BLOCK("NodeManager::insertNodeToBucket: hash_it != kind_bucket.end()");
            // linear search in the small bucket
            for(const auto& pair : hash_it->second) {
                // optimize comparison order: the most likely different ones are in front, to avoid the expensive isEquivalentTo
                if(pair.first.get() == node.get()) {
                    // completely the same pointer, return directly
                    return nodes[pair.second];
                }
                // fast structure comparison (avoid the expensive isEquivalentTo call)
                if(pair.first->getKind() == node->getKind() &&
                   pair.first->getChildrenSize() == node->getChildrenSize() &&
                   pair.first->getName() == node->getName()) {
                    // only call the expensive isEquivalentTo when the structure matches completely
                    if(pair.first->isEquivalentTo(*node)) {
                        return nodes[pair.second];
                    }
                }
            }
        }
        
        // node does not exist, insert new node
        size_t new_index = nodes.size();
        kind_bucket[node_hash].emplace_back(node, new_index);
        nodes.emplace_back(node);
        return node;
    }

    void NodeManager::initializeStaticNodes() {
        // Basic constants
        insertNodeToBucket(NULL_NODE);
        insertNodeToBucket(UNKNOWN_NODE);
        insertNodeToBucket(TRUE_NODE);
        insertNodeToBucket(FALSE_NODE);
        insertNodeToBucket(E_NODE);
        insertNodeToBucket(PI_NODE);
        insertNodeToBucket(NAN_NODE);
        insertNodeToBucket(EPSILON_NODE);
        insertNodeToBucket(POS_EPSILON_NODE);
        insertNodeToBucket(NEG_EPSILON_NODE);
        
        // Infinity nodes
        insertNodeToBucket(STR_INF_NODE);
        insertNodeToBucket(STR_POS_INF_NODE);
        insertNodeToBucket(STR_NEG_INF_NODE);
        insertNodeToBucket(INT_INF_NODE);
        insertNodeToBucket(INT_POS_INF_NODE);
        insertNodeToBucket(INT_NEG_INF_NODE);
        insertNodeToBucket(REAL_INF_NODE);
        insertNodeToBucket(REAL_POS_INF_NODE);
        insertNodeToBucket(REAL_NEG_INF_NODE);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name, std::vector<std::shared_ptr<DAGNode>> children) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind, name, children);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind, name);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, NODE_KIND kind) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, kind);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode() {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>();
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(NODE_KIND kind, std::string name) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(kind, name);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(NODE_KIND kind) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(kind);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const Integer& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const Real& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const double& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const int& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(std::shared_ptr<Sort> sort, const bool& v) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(sort, v);
        return insertNodeToBucket(node);
    }

    std::shared_ptr<DAGNode> NodeManager::createNode(const std::string& n) {
        TIME_FUNC();
        auto node = std::make_shared<DAGNode>(n);
        return insertNodeToBucket(node);
    }

}
