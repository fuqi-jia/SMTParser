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

    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& node, boost::unordered_map<std::shared_ptr<DAGNode>, std::string>& visited){
        if(visited.find(node) != visited.end()){
            return visited[node];
        }
        std::string res = "";

        // switch on the kind of the node
        auto kind = node->getKind();
        switch (kind)
        {
        case NODE_KIND::NT_UNKNOWN:
            std::cout<<"Unknown kind"<<std::endl;
            assert(false);
            break;
        case NODE_KIND::NT_ERROR:
            std::cout<<"Error kind"<<std::endl;
            assert(false);
            break;
        case NODE_KIND::NT_NULL:
            std::cout<<"Null kind"<<std::endl;
            assert(false);
            res = "NULL";
            break;
        case NODE_KIND::NT_CONST_TRUE:
            res = "true";
            break;
        case NODE_KIND::NT_CONST_FALSE:
            res = "false";
            break;
        // CORE OPERATORS
        case NODE_KIND::NT_EQ:
        case NODE_KIND::NT_EQ_BOOL:
        case NODE_KIND::NT_EQ_OTHER:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_DISTINCT:
        case NODE_KIND::NT_DISTINCT_BOOL:
        case NODE_KIND::NT_DISTINCT_OTHER:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        // CONSTANT / VARIABLE
        case NODE_KIND::NT_CONST:
            res = dumpConst(node->getName(), node->getSort());
            break;
        case NODE_KIND::NT_VAR:
            res = node->getName();
            break;
        // BOOLEAN
        case NODE_KIND::NT_NOT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_AND:
        case NODE_KIND::NT_OR:
        case NODE_KIND::NT_IMPLIES:
        case NODE_KIND::NT_XOR:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        // UF
        case NODE_KIND::NT_APPLY_UF:
            res = "APPLY_UF";
            break;
        // ARITHMATIC COMMON OPERATORS
        case NODE_KIND::NT_ADD:
        case NODE_KIND::NT_MUL:
        case NODE_KIND::NT_IAND:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_POW2:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_POW:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_SUB:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_NEG:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_DIV_INT:
        case NODE_KIND::NT_DIV_REAL:
        case NODE_KIND::NT_MOD:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_ABS:
        case NODE_KIND::NT_SQRT:
        case NODE_KIND::NT_CEIL:
        case NODE_KIND::NT_FLOOR:
        case NODE_KIND::NT_ROUND:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // TRANSCENDENTAL ARITHMATIC
        case NODE_KIND::NT_EXP:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_LOG:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
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
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_LE:
        case NODE_KIND::NT_LT:
        case NODE_KIND::NT_GE:
        case NODE_KIND::NT_GT:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // ARITHMATIC CONVERSION
        case NODE_KIND::NT_TO_INT:
        case NODE_KIND::NT_TO_REAL:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // ARITHMATIC PROPERTIES
        case NODE_KIND::NT_IS_INT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_IS_DIVISIBLE:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_IS_PRIME:
        case NODE_KIND::NT_IS_EVEN:
        case NODE_KIND::NT_IS_ODD:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // ARITHMATIC CONSTANTS
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
        case NODE_KIND::NT_GCD:
        case NODE_KIND::NT_LCM:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_FACT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // BITVECTOR COMMON OPERATORS
        // Bit-wise operations
        case NODE_KIND::NT_BV_NOT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_BV_AND:
        case NODE_KIND::NT_BV_OR:
        case NODE_KIND::NT_BV_XOR:
        case NODE_KIND::NT_BV_NAND:
        case NODE_KIND::NT_BV_NOR:
        case NODE_KIND::NT_BV_XNOR:
        case NODE_KIND::NT_BV_COMP:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        // Arithmetic operations
        case NODE_KIND::NT_BV_NEG:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_BV_ADD:
        case NODE_KIND::NT_BV_SUB:
        case NODE_KIND::NT_BV_MUL:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_BV_UDIV:
        case NODE_KIND::NT_BV_SDIV:
        case NODE_KIND::NT_BV_UREM:
        case NODE_KIND::NT_BV_SREM:
        case NODE_KIND::NT_BV_UMOD:
        case NODE_KIND::NT_BV_SMOD:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // Arithmetic operations with overflow
        case NODE_KIND::NT_BV_NEGO:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_BV_SADDO:
        case NODE_KIND::NT_BV_UADDO:
        case NODE_KIND::NT_BV_SMULO:
        case NODE_KIND::NT_BV_UMULO:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_BV_SDIVO:
        case NODE_KIND::NT_BV_UDIVO:
        case NODE_KIND::NT_BV_SREMO:
        case NODE_KIND::NT_BV_UREMO:
        case NODE_KIND::NT_BV_SMODO:
        case NODE_KIND::NT_BV_UMODO:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // Shift operations
        case NODE_KIND::NT_BV_SHL:
        case NODE_KIND::NT_BV_LSHR:
        case NODE_KIND::NT_BV_ASHR:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // Function
        case NODE_KIND::NT_BV_CONCAT:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_BV_EXTRACT:
            res = "((_ extract " + dumpSMTLIB2(node->getChild(1), visited) + " " + dumpSMTLIB2(node->getChild(2), visited) + ") " + dumpSMTLIB2(node->getChild(0), visited) + ")";
            break;
        case NODE_KIND::NT_BV_REPEAT:
        case NODE_KIND::NT_BV_ZERO_EXT:
        case NODE_KIND::NT_BV_SIGN_EXT:
        case NODE_KIND::NT_BV_ROTATE_LEFT:
        case NODE_KIND::NT_BV_ROTATE_RIGHT:
            res = "((_ " + kindToString(kind) + " " + dumpSMTLIB2(node->getChild(1), visited) + ") " + dumpSMTLIB2(node->getChild(0), visited) + ")";
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
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // BITVECTOR CONVERSION
        case NODE_KIND::NT_BV_TO_NAT:
        case NODE_KIND::NT_NAT_TO_BV:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // FLOATING POINT COMMON OPERATORS
        case NODE_KIND::NT_FP_ADD:
        case NODE_KIND::NT_FP_SUB:
        case NODE_KIND::NT_FP_MUL:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_FP_DIV:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_FP_ABS:
        case NODE_KIND::NT_FP_NEG:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_FP_REM:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_FP_FMA:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        case NODE_KIND::NT_FP_SQRT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_FP_MIN:
        case NODE_KIND::NT_FP_MAX:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        // FLOATING POINT COMP
        case NODE_KIND::NT_FP_LE:
        case NODE_KIND::NT_FP_LT:
        case NODE_KIND::NT_FP_GE:
        case NODE_KIND::NT_FP_GT:
        case NODE_KIND::NT_FP_EQ:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // FLOATING POINT CONVERSION
        case NODE_KIND::NT_FP_TO_UBV:
        case NODE_KIND::NT_FP_TO_SBV:
        case NODE_KIND::NT_FP_TO_REAL:
        case NODE_KIND::NT_FP_TO_FP:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // FLOATING POINT PROPERTIES
        case NODE_KIND::NT_FP_IS_NORMAL:
        case NODE_KIND::NT_FP_IS_SUBNORMAL:
        case NODE_KIND::NT_FP_IS_ZERO:
        case NODE_KIND::NT_FP_IS_INF:
        case NODE_KIND::NT_FP_IS_NAN:
        case NODE_KIND::NT_FP_IS_NEG:
        case NODE_KIND::NT_FP_IS_POS:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // ARRAY
        case NODE_KIND::NT_SELECT:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_STORE:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        // STRINGS COMMON OPERATORS
        case NODE_KIND::NT_STR_LEN:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_STR_CONCAT:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_STR_SUBSTR:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        case NODE_KIND::NT_STR_PREFIXOF:
        case NODE_KIND::NT_STR_SUFFIXOF:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_STR_INDEXOF:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        case NODE_KIND::NT_STR_CHARAT: 
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_STR_UPDATE:
        case NODE_KIND::NT_STR_REPLACE:
        case NODE_KIND::NT_STR_REPLACE_ALL:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        case NODE_KIND::NT_STR_TO_LOWER:
        case NODE_KIND::NT_STR_TO_UPPER:
        case NODE_KIND::NT_STR_REV:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_STR_SPLIT:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // STRINGS COMP
        case NODE_KIND::NT_STR_LT:
        case NODE_KIND::NT_STR_LE:
        case NODE_KIND::NT_STR_GT:
        case NODE_KIND::NT_STR_GE:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        // STRINGS PROPERTIES
        case NODE_KIND::NT_STR_IN_REG:
        case NODE_KIND::NT_STR_CONTAINS:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_STR_IS_DIGIT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // STRINGS CONVERSION
        case NODE_KIND::NT_STR_FROM_INT:
        case NODE_KIND::NT_STR_TO_INT:
        case NODE_KIND::NT_STR_TO_REG:
        case NODE_KIND::NT_STR_TO_CODE:
        case NODE_KIND::NT_STR_FROM_CODE:
            res = dumpSingleOp(kind, node->getChild(0), visited);
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
        case NODE_KIND::NT_REG_CONCAT:
        case NODE_KIND::NT_REG_UNION:
        case NODE_KIND::NT_REG_INTER:
        case NODE_KIND::NT_REG_DIFF:
            res = dumpChainOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_REG_STAR:
        case NODE_KIND::NT_REG_PLUS:
        case NODE_KIND::NT_REG_OPT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        case NODE_KIND::NT_REG_RANGE:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_REG_REPEAT:
            res = dumpDoubleOp(kind, node->getChild(0), node->getChild(1), visited);
            break;
        case NODE_KIND::NT_REG_LOOP:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        case NODE_KIND::NT_REG_COMPLEMENT:
            res = dumpSingleOp(kind, node->getChild(0), visited);
            break;
        // STRINGS RE FUNCTIONS
        case NODE_KIND::NT_REPLACE_REG:
        case NODE_KIND::NT_REPLACE_REG_ALL:
        case NODE_KIND::NT_INDEXOF_REG:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        // LET, FROM HERE TODO
        case NODE_KIND::NT_LET:
            res = dumpSMTLIB2(node->getChild(0), visited);
            break;
        // ITE
        case NODE_KIND::NT_ITE:
            res = dumpTripleOp(kind, node->getChild(0), node->getChild(1), node->getChild(2), visited);
            break;
        // QUANTIFIERS
        case NODE_KIND::NT_FORALL:
        case NODE_KIND::NT_EXISTS:
            res = dumpQuantOp(kind, node->getChildren(), visited);
            break;
        case NODE_KIND::NT_QUANT_VAR:
            res = node->getName();
            break;
        // FUNC
        case NODE_KIND::NT_FUNC_DEC:
            res = node->getName();
            break;
        case NODE_KIND::NT_FUNC_DEF:
            res = node->getName();
            break;
        case NODE_KIND::NT_FUNC_PARAM:
            res = node->getName();
            break;
        case NODE_KIND::NT_FUNC_APPLY:{
            res = "(" + node->getName();
            for(size_t i=1;i<node->getChildrenSize();i++){
                res += " " + dumpSMTLIB2(node->getChild(i), visited);
            }
            res += ")";
            break;
        }
        default:
            res = "UNKNOWN_KIND";
        }

        visited[node] = res;
        return res;
    }
    
    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& node){
        boost::unordered_map<std::shared_ptr<DAGNode>, std::string> visited;
        return dumpSMTLIB2(node, visited);
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
        std::string res = "(assert ";
        for(size_t i=0;i<assertions.size();i++){
            res += dumpSMTLIB2(assertions[i]);
        }
        res += ")";
        return res;
    }
}