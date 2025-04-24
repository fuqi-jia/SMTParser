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
#include <set>
#include <stack>
#include <unordered_map>

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

    std::string dumpSingleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& p, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        return "(" + kindToString(kind) + " " + dumpSMTLIB2(p, visited) + ")";
    }

    std::string dumpDoubleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& r, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        return "(" + kindToString(kind) + " " + dumpSMTLIB2(l, visited) + " " + dumpSMTLIB2(r, visited) + ")";
    }

    std::string dumpTripleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& m, const std::shared_ptr<DAGNode>& r, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        return "(" + kindToString(kind) + " " + dumpSMTLIB2(l, visited) + " " + dumpSMTLIB2(m, visited) + " " + dumpSMTLIB2(r, visited) + ")";
    }

    std::string dumpChainOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        std::string res = "(" + kindToString(kind);
        for (auto& node : p){
            res += " " + dumpSMTLIB2(node, visited);
        }
        res += ")";
        return res;
    }

    std::string dumpQuantOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        std::string res = "(" + kindToString(kind) + " (";
        for(size_t i=1;i<p.size();i++){
            if(i==1) res += "(" + dumpSMTLIB2(p[i], visited) + " " + p[i]->getSort()->toString() + ")";
            else res += " (" + dumpSMTLIB2(p[i], visited) + " " + p[i]->getSort()->toString() + ")";
        }
        res += ") ";
        res += dumpSMTLIB2(p[0], visited);
        res += ")";
        return res;
    }

    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& node){
        // 使用std::unordered_map替代boost::unordered_map，解决头文件依赖问题
        std::unordered_map<std::shared_ptr<DAGNode>, std::string> visited;
        std::unordered_map<std::shared_ptr<DAGNode>, bool> in_process;
        
        // 使用栈来保存待处理的节点，避免递归
        std::stack<std::shared_ptr<DAGNode>> node_stack;
        std::stack<int> process_states; // 用于跟踪节点处理的阶段
        
        // 初始节点入栈
        node_stack.push(node);
        process_states.push(0); // 0表示初始状态
        
        while(!node_stack.empty()) {
            std::shared_ptr<DAGNode> current = node_stack.top();
            int state = process_states.top();
            process_states.pop();
            
            // 如果节点已处理完，弹出并继续
            if(visited.find(current) != visited.end()) {
                node_stack.pop();
                continue;
            }
            
            // 如果节点正在处理中（标记但未完成），这可能是循环引用
            if(in_process.find(current) != in_process.end() && in_process[current]) {
                visited[current] = current->getName() + "_循环引用";
                node_stack.pop();
                continue;
            }
            
            // 标记节点为处理中
            in_process[current] = true;
            
            // 根据状态处理节点
            switch(state) {
                case 0: { // 初始状态，检查子节点
                    // 更新状态并重新入栈，下一次pop时将处理这个节点
                    process_states.push(1);
                    
                    // 当前节点没有子节点或者是简单类型，直接处理
                    if(current->getChildrenSize() == 0 || 
                       current->getKind() == NODE_KIND::NT_CONST ||
                       current->getKind() == NODE_KIND::NT_VAR ||
                       current->getKind() == NODE_KIND::NT_FUNC_PARAM ||
                       current->getKind() == NODE_KIND::NT_CONST_TRUE ||
                       current->getKind() == NODE_KIND::NT_CONST_FALSE ||
                       current->getKind() == NODE_KIND::NT_PI ||
                       current->getKind() == NODE_KIND::NT_E ||
                       current->getKind() == NODE_KIND::NT_INFINITY ||
                       current->getKind() == NODE_KIND::NT_NAN ||
                       current->getKind() == NODE_KIND::NT_EPSILON ||
                       current->getKind() == NODE_KIND::NT_REG_NONE ||
                       current->getKind() == NODE_KIND::NT_REG_ALL ||
                       current->getKind() == NODE_KIND::NT_REG_ALLCHAR) {
                        state = 1;
                        process_states.pop(); // 移除刚才添加的状态
                        process_states.push(1); // 直接进入处理阶段
                    } else {
                        // 将所有子节点入栈
                        for(int i = current->getChildrenSize() - 1; i >= 0; i--) {
                            if(visited.find(current->getChild(i)) == visited.end()) {
                                node_stack.push(current->getChild(i));
                                process_states.push(0);
                            }
                        }
                    }
                    break;
                }
                case 1: { // 所有子节点已处理，处理当前节点
                    std::string result;
                    auto kind = current->getKind();
                    
                    switch(kind) {
                        case NODE_KIND::NT_UNKNOWN:
                            result = "UNKNOWN";
                            break;
                        case NODE_KIND::NT_ERROR:
                            result = "ERROR";
                            break;
                        case NODE_KIND::NT_NULL:
                            result = "NULL";
                            break;
                        case NODE_KIND::NT_CONST_TRUE:
                            result = "true";
                            break;
                        case NODE_KIND::NT_CONST_FALSE:
                            result = "false";
                            break;
                        case NODE_KIND::NT_CONST:
                            result = dumpConst(current->getName(), current->getSort());
                            break;
                        case NODE_KIND::NT_VAR:
                        case NODE_KIND::NT_QUANT_VAR:
                        case NODE_KIND::NT_FUNC_DEC:
                        case NODE_KIND::NT_FUNC_DEF:
                        case NODE_KIND::NT_FUNC_PARAM:
                            result = current->getName();
                            break;
                        case NODE_KIND::NT_PI:
                            result = "pi";
                            break;
                        case NODE_KIND::NT_E:
                            result = "e";
                            break;
                        case NODE_KIND::NT_INFINITY:
                            result = "inf";
                            break;
                        case NODE_KIND::NT_NAN:
                            result = "NaN";
                            break;
                        case NODE_KIND::NT_EPSILON:
                            result = "epsilon";
                            break;
                        case NODE_KIND::NT_REG_NONE:
                            result = "re.none";
                            break;
                        case NODE_KIND::NT_REG_ALL:
                            result = "re.all";
                            break;
                        case NODE_KIND::NT_REG_ALLCHAR:
                            result = "re.allchar";
                            break;
                        case NODE_KIND::NT_NOT:
                        case NODE_KIND::NT_POW2:
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
                        case NODE_KIND::NT_TAN:
                        case NODE_KIND::NT_TO_INT:
                        case NODE_KIND::NT_TO_REAL:
                        case NODE_KIND::NT_IS_INT:
                        case NODE_KIND::NT_IS_PRIME:
                        case NODE_KIND::NT_IS_EVEN:
                        case NODE_KIND::NT_IS_ODD:
                        case NODE_KIND::NT_FACT:
                        case NODE_KIND::NT_BV_NOT:
                        case NODE_KIND::NT_BV_NEG:
                        case NODE_KIND::NT_BV_TO_NAT:
                        case NODE_KIND::NT_NAT_TO_BV:
                        case NODE_KIND::NT_FP_ABS:
                        case NODE_KIND::NT_FP_NEG:
                        case NODE_KIND::NT_FP_SQRT:
                        case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
                        case NODE_KIND::NT_FP_TO_UBV:
                        case NODE_KIND::NT_FP_TO_SBV:
                        case NODE_KIND::NT_FP_TO_REAL:
                        case NODE_KIND::NT_FP_TO_FP:
                        case NODE_KIND::NT_FP_IS_NORMAL:
                        case NODE_KIND::NT_FP_IS_SUBNORMAL:
                        case NODE_KIND::NT_FP_IS_ZERO:
                        case NODE_KIND::NT_FP_IS_INF:
                        case NODE_KIND::NT_FP_IS_NAN:
                        case NODE_KIND::NT_FP_IS_NEG:
                        case NODE_KIND::NT_FP_IS_POS:
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
                            // 单操作数
                            result = "(" + kindToString(kind) + " " + visited[current->getChild(0)] + ")";
                            break;
                        
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
                            // 双操作数
                            result = "(" + kindToString(kind) + " " + visited[current->getChild(0)] + " " + visited[current->getChild(1)] + ")";
                            break;
                            
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
                            // 三操作数
                            result = "(" + kindToString(kind) + " " + visited[current->getChild(0)] + " " + visited[current->getChild(1)] + " " + visited[current->getChild(2)] + ")";
                            break;
                            
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
                        case NODE_KIND::NT_REG_DIFF:
                            // 多操作数
                            {
                                result = "(" + kindToString(kind);
                                for(size_t i = 0; i < current->getChildrenSize(); i++) {
                                    result += " " + visited[current->getChild(i)];
                                }
                                result += ")";
                            }
                            break;
                            
                        case NODE_KIND::NT_BV_EXTRACT:
                            result = "((_ extract " + visited[current->getChild(1)] + " " + visited[current->getChild(2)] + ") " + visited[current->getChild(0)] + ")";
                            break;
                            
                        case NODE_KIND::NT_BV_REPEAT:
                        case NODE_KIND::NT_BV_ZERO_EXT:
                        case NODE_KIND::NT_BV_SIGN_EXT:
                        case NODE_KIND::NT_BV_ROTATE_LEFT:
                        case NODE_KIND::NT_BV_ROTATE_RIGHT:
                            result = "((_ " + kindToString(kind) + " " + visited[current->getChild(1)] + ") " + visited[current->getChild(0)] + ")";
                            break;
                            
                        case NODE_KIND::NT_LET:
                            result = visited[current->getChild(0)];
                            break;
                            
                        case NODE_KIND::NT_FORALL:
                        case NODE_KIND::NT_EXISTS:
                            {
                                result = "(" + kindToString(kind) + " (";
                                for(size_t i = 1; i < current->getChildrenSize(); i++){
                                    if(i == 1) result += "(" + visited[current->getChild(i)] + " " + current->getChild(i)->getSort()->toString() + ")";
                                    else result += " (" + visited[current->getChild(i)] + " " + current->getChild(i)->getSort()->toString() + ")";
                                }
                                result += ") ";
                                result += visited[current->getChild(0)];
                                result += ")";
                            }
                            break;
                            
                        case NODE_KIND::NT_FUNC_APPLY:
                            {
                                result = "(" + current->getName();
                                for(size_t i = 1; i < current->getChildrenSize(); i++){
                                    result += " " + visited[current->getChild(i)];
                                }
                                result += ")";
                            }
                            break;
                            
                        default:
                            result = "UNKNOWN_KIND";
                    }
                    
                    visited[current] = result;
                    in_process[current] = false;
                    node_stack.pop();
                    break;
                }
            }
        }
        
        return visited[node];
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
}