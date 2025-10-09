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
#include <unordered_set>

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
            uint8_t action; // 0=process, 1=space, 2=close_paren, 3=close_paren_space, 4=text_output

            WorkItem(DAGNode* n, uint8_t a = 0) : node(n), action(a) {}
            
            // For text output
            std::string text;
            WorkItem(const std::string& t, uint8_t a = 4) : node(nullptr), action(a), text(t) {}
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
            if (item.action == 4) { // Write text
                out << item.text;
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
                if (node->getName() == "(fp_bit_representation)" && node->getChildrenSize() == 3) {
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
                } else {
                    out << dumpConst(node->getName(), node->getSort());
                }
                break;
            case NODE_KIND::NT_VAR:
            case NODE_KIND::NT_TEMP_VAR:
            case NODE_KIND::NT_PLACEHOLDER_VAR:
                out << node->getName();
                break;
            case NODE_KIND::NT_CONST_ARRAY: {
                out << "((as const ";
                out << node->getSort()->toString();
                out << ") ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(node->getChild(0).get(), 0);   // child0
                break;
            }

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
                
                // Output: (let ((var1 value1) (var2 value2) ...) body)
                // Stack order (reverse): ) + body + ") " + bindings + "(let ("
                
                work_stack.emplace_back(")", 4);  // final )
                work_stack.emplace_back(node->getChild(0).get(), 0);  // body
                work_stack.emplace_back(") ", 4);  // close binding list and add space
                
                // Process bindings in reverse order for stack
                for(int i = node->getChildrenSize() - 1; i >= 1; i--){
                    work_stack.emplace_back(")", 4);  // ) for this binding
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), 0);  // binding value
                    work_stack.emplace_back(" ", 4);  // space before value
                    work_stack.emplace_back(node->getChild(i)->getPureName(), 4);  // variable name
                    work_stack.emplace_back("(", 4);  // ( for this binding
                    if (i > 1) {
                        work_stack.emplace_back(" ", 4);  // space between bindings
                    }
                }
                
                work_stack.emplace_back("(let (", 4);  // opening
                break;
            }
            case NODE_KIND::NT_LET_CHAIN: {
                // For let-chain: (let ((var1 val1)) (let ((var2 val2)) body))
                // This creates nested let expressions
                
                size_t num_bindings = node->getChildrenSize() - 1;
                
                // Add closing parentheses for all let expressions (in reverse order)
                for(size_t i = 0; i < num_bindings; i++){
                    work_stack.emplace_back(")", 4);  // ) for each let
                }
                
                // Add body
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), 0);
                
                // Process let bindings in reverse order
                for(int i = num_bindings - 1; i >= 0; i--){
                    condAssert(node->getChild(i)->isLetBindVarList(), "NT_LET_CHAIN: child is not LET_BIND_VAR_LIST");
                    auto var_list = node->getChild(i);
                    
                    work_stack.emplace_back(") ", 4);  // close binding list and add space
                    
                    // Process variables in this binding list (reverse order)
                    for(int j = var_list->getChildrenSize() - 1; j >= 0; j--){
                        work_stack.emplace_back(")", 4);  // ) for binding
                        work_stack.emplace_back(var_list->getChild(j)->getChild(0).get(), 0);  // binding value
                        work_stack.emplace_back(" ", 4);  // space before value
                        work_stack.emplace_back(var_list->getChild(j)->getPureName(), 4);  // variable name
                        work_stack.emplace_back("(", 4);  // ( for binding
                        if(j > 0) {
                            work_stack.emplace_back(" ", 4);  // space between bindings
                        }
                    }
                    
                    work_stack.emplace_back("(let (", 4);  // let opening
                }
                
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR: {
                out << node->getPureName();
                break;
            }
            case NODE_KIND::NT_LET_BIND_VAR_LIST: {
                // Output: ( (var1 value1) (var2 value2) ... )
                // Stack order (reverse): ) + bindings + "( "
                
                work_stack.emplace_back(")", 4);  // final )
                
                // Process bindings in reverse order for stack
                for(int i = node->getChildrenSize() - 1; i >= 1; i--){
                    work_stack.emplace_back(")", 4);  // ) for this binding
                    work_stack.emplace_back(node->getChild(i)->getChild(0).get(), 0);  // binding value
                    work_stack.emplace_back(" ", 4);  // space before value
                    work_stack.emplace_back(node->getChild(i)->getPureName(), 4);  // variable name
                    work_stack.emplace_back("(", 4);  // ( for this binding
                    if (i > 1) {
                        work_stack.emplace_back(" ", 4);  // space between bindings
                    }
                }
                
                work_stack.emplace_back("( ", 4);  // opening "( "
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
                
                if(node->getChildrenSize() == 4) {
                    // 4-parameter version: ((_ to_fp eb sb) rm param)
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
                } else if(node->getChildrenSize() == 3) {
                    // 3-parameter version: ((_ to_fp eb sb) param)
                    auto param = node->getChild(2).get();
                    out << "((_ to_fp ";
                    work_stack.emplace_back(nullptr, 2);  // )
                    work_stack.emplace_back(param, 0);    // param
                    work_stack.emplace_back(nullptr, 3);  // ") "
                    work_stack.emplace_back(sb, 0);       // sb
                    work_stack.emplace_back(nullptr, 1);  // space
                    work_stack.emplace_back(eb, 0);       // eb
                } else {
                    // Invalid number of children
                    out << "INVALID_FP_TO_FP_NODE";
                }
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

            case NODE_KIND::NT_ROOT_OBJ: {
                auto expr = node->getChild(0).get();
                auto index = node->getChild(1).get();
                out << "(root-obj ";
                work_stack.emplace_back(nullptr, 2);  // )
                work_stack.emplace_back(index, 0);    // index
                work_stack.emplace_back(nullptr, 1);  // space
                work_stack.emplace_back(expr, 0);     // expr
                break;
            }

            case NODE_KIND::NT_ROOT_OF_WITH_INTERVAL: {
                out << "(root-of-with-interval (coeffs ";
                
                // Stack order (LIFO - Last In First Out):
                // We want output: (root-of-with-interval (coeffs c1 c2 ...) lower upper)
                // So we push in reverse order:
                
                // 1. Push closing parenthesis for root-of-with-interval (will be printed last)
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 2. Push upper bound
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 1).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 3. Push lower bound
                work_stack.emplace_back(node->getChild(node->getChildrenSize() - 2).get(), 0);
                work_stack.emplace_back(nullptr, 1);  // space
                
                // 4. Push closing parenthesis for coeffs list
                work_stack.emplace_back(nullptr, 2);  // )
                
                // 5. Push coefficients in reverse order (so they print in correct order)
                for(int i = node->getChildrenSize() - 3; i >= 0; i--) {
                    work_stack.emplace_back(node->getChild(i).get(), 0);
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
        dumpSMTLIB2_streaming(root, oss);  // enable cache by default
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

    // NodeManager
    
    // Static constant nodes are now defined inline in the header file

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
        // Clear non-static nodes only (preserve static constants)
        for (size_t i = static_node_count; i < nodes.size(); i++) {
            nodes[i]->clear();
        }
        nodes.clear();
        
        // Clear hash buckets and re-insert static nodes
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
                    auto node_ptr = nodes[pair.second];
                    node_ptr->incUseCount();
                    return node_ptr;
                }
                // fast structure comparison (avoid the expensive isEquivalentTo call)
                if(pair.first->getKind() == node->getKind() &&
                   pair.first->getChildrenSize() == node->getChildrenSize() &&
                   pair.first->getName() == node->getName()) {
                    // only call the expensive isEquivalentTo when the structure matches completely
                    if(pair.first->isEquivalentTo(*node)) {
                        auto node_ptr = nodes[pair.second];
                        node_ptr->incUseCount();
                        return node_ptr;
                    }
                }
            }
        }
        
        // node does not exist, insert new node
        size_t new_index = nodes.size();
        kind_bucket[node_hash].emplace_back(node, new_index);
        nodes.emplace_back(node);
        node->incUseCount();
        return node;
    }

    void NodeManager::initializeStaticNodes() {
        // Basic constants
        insertNodeToBucket(NULL_NODE);
        insertNodeToBucket(UNKNOWN_NODE);
        insertNodeToBucket(ERROR_NODE);
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
        
        // Mark how many nodes are static constants so we can preserve them during clear()
        static_node_count = nodes.size();
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
