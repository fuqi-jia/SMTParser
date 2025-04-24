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


    // 迭代版本的dumpSMTLIB2函数，避免栈溢出
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& root) {
        if (!root) return "";
        
        // 处理结果映射，缓存已处理的节点，避免重复处理
        boost::unordered_map<std::shared_ptr<DAGNode>, std::string> results;
        
        // 处理栈，用于实现后序遍历
        std::stack<std::shared_ptr<DAGNode>> todo;
        
        // 记录已经访问过的节点，避免重复添加到栈中
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        
        // 记录每个节点的处理状态（用于确定是否所有子节点都已处理）
        boost::unordered_map<std::shared_ptr<DAGNode>, bool> processed;
        
        // 初始化栈，从根节点开始遍历
        todo.push(root);
        
        while (!todo.empty()) {
            std::shared_ptr<DAGNode> current = todo.top();
            
            // 如果当前节点已经处理过了，直接弹出
            if (results.find(current) != results.end()) {
                todo.pop();
                continue;
            }
            
            // 如果是首次访问节点，标记为已访问
            if (visited.find(current) == visited.end()) {
                visited.insert(current);
                processed[current] = false;
            }
            
            // 如果所有子节点都已处理，处理当前节点
            if (processed[current]) {
                std::string res = "";
                auto kind = current->getKind();
                
                switch (kind) {
                // 基本类型和常量处理
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
                
                // 常量和变量
                case NODE_KIND::NT_CONST:
                    res = dumpConst(current->getName(), current->getSort());
                    break;
                case NODE_KIND::NT_VAR:
                    res = current->getName();
                    break;
                    
                // 单元操作符 - 接受一个参数
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
                    
                // 二元操作符 - 接受两个参数
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
                    
                // 三元操作符 - 接受三个参数
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
                    
                // 多参数操作符 - 接受任意数量参数
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
                    
                // 特殊处理的操作符
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
                    
                // 常量
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
                    
                // 量词
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
                    
                // 函数相关
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
            
            // 判断是否需要添加子节点
            bool allChildrenProcessed = true;
            for (auto& child : current->getChildren()) {
                if (results.find(child) == results.end()) {
                    allChildrenProcessed = false;
                    todo.push(child);
                }
            }
            
            if (!allChildrenProcessed) {
                // 如果有未处理的子节点，先等待所有子节点处理完毕
                processed[current] = false;
            } else {
                // 如果所有子节点都已处理完毕，标记当前节点处理状态为true
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
}