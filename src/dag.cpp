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

    // dump SMT-LIB2 format
    std::string dumpSMTLIB2(const std::vector<DAGNode>& assertions){
        std::string res = "";

        for (auto& node : assertions){
            res += "(assert " + node.dumpSMTLIB2() + ")\n";
        }

        return res;
    }

    std::string dumpSingleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& p){
        return "(" + kindToString(kind) + " " + p->dumpSMTLIB2() + ")";
    }

    std::string dumpDoubleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& r){
        return "(" + kindToString(kind) + " " + l->dumpSMTLIB2() + " " + r->dumpSMTLIB2() + ")";
    }

    std::string dumpTripleOp(const NODE_KIND& kind, const std::shared_ptr<DAGNode>& l, const std::shared_ptr<DAGNode>& m, const std::shared_ptr<DAGNode>& r){
        return "(" + kindToString(kind) + " " + l->dumpSMTLIB2() + " " + m->dumpSMTLIB2() + " " + r->dumpSMTLIB2() + ")";
    }

    std::string dumpChainOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p){
        std::string res = "(" + kindToString(kind);
        for (auto& node : p){
            res += " " + node->dumpSMTLIB2();
        }
        res += ")";
        return res;
    }

    std::string dumpQuantOp(const NODE_KIND& kind, const std::vector<std::shared_ptr<DAGNode>>& p){
        std::string res = "(" + kindToString(kind) + " (";
        for(size_t i=1;i<p.size();i++){
            if(i==1) res += "(" + p[i]->dumpSMTLIB2() + " " + p[i]->getSort()->toString() + ")";
            else res += " (" + p[i]->dumpSMTLIB2() + " " + p[i]->getSort()->toString() + ")";
        }
        res += ") ";
        res += p[0]->dumpSMTLIB2();
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

    std::string DAGNode::dumpSMTLIB2() const{
        std::string res = "";
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
            return "NULL";
        case NODE_KIND::NT_CONST_TRUE:
            return "true";
        case NODE_KIND::NT_CONST_FALSE:
            return "false";
        // CORE OPERATORS
        case NODE_KIND::NT_EQ:
        case NODE_KIND::NT_EQ_BOOL:
        case NODE_KIND::NT_EQ_OTHER:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_DISTINCT:
        case NODE_KIND::NT_DISTINCT_BOOL:
        case NODE_KIND::NT_DISTINCT_OTHER:
            return dumpChainOp(kind, children);
        // CONSTANT / VARIABLE
        case NODE_KIND::NT_CONST:
            return dumpConst(name, sort);
        case NODE_KIND::NT_VAR:
            return name;
        // BOOLEAN
        case NODE_KIND::NT_NOT:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_AND:
        case NODE_KIND::NT_OR:
        case NODE_KIND::NT_IMPLIES:
        case NODE_KIND::NT_XOR:
            return dumpChainOp(kind, children);
        // UF
        case NODE_KIND::NT_APPLY_UF:
            return "APPLY_UF";
        // ARITHMATIC COMMON OPERATORS
        case NODE_KIND::NT_ADD:
        case NODE_KIND::NT_MUL:
        case NODE_KIND::NT_IAND:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_POW2:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_POW:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_SUB:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_NEG:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_DIV_INT:
        case NODE_KIND::NT_DIV_REAL:
        case NODE_KIND::NT_MOD:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_ABS:
        case NODE_KIND::NT_SQRT:
        case NODE_KIND::NT_CEIL:
        case NODE_KIND::NT_FLOOR:
        case NODE_KIND::NT_ROUND:
            return dumpSingleOp(kind, children[0]);
        // TRANSCENDENTAL ARITHMATIC
        case NODE_KIND::NT_EXP:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_LOG:
            return dumpDoubleOp(kind, children[0], children[1]);
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
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_LE:
        case NODE_KIND::NT_LT:
        case NODE_KIND::NT_GE:
        case NODE_KIND::NT_GT:
            return dumpDoubleOp(kind, children[0], children[1]);
        // ARITHMATIC CONVERSION
        case NODE_KIND::NT_TO_INT:
        case NODE_KIND::NT_TO_REAL:
            return dumpSingleOp(kind, children[0]);
        // ARITHMATIC PROPERTIES
        case NODE_KIND::NT_IS_INT:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_IS_DIVISIBLE:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_IS_PRIME:
        case NODE_KIND::NT_IS_EVEN:
        case NODE_KIND::NT_IS_ODD:
            return dumpSingleOp(kind, children[0]);
        // ARITHMATIC CONSTANTS
        case NODE_KIND::NT_PI:
            return "PI";
        case NODE_KIND::NT_E:
            return "E";
        case NODE_KIND::NT_INFINITY:
            return "INF";
        case NODE_KIND::NT_NAN:
            return "NaN";
        case NODE_KIND::NT_EPSILON:
            return "EPSILON";
        case NODE_KIND::NT_GCD:
        case NODE_KIND::NT_LCM:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_FACT:
            return dumpSingleOp(kind, children[0]);
        // BITVECTOR COMMON OPERATORS
        // Bit-wise operations
        case NODE_KIND::NT_BV_NOT:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_BV_AND:
        case NODE_KIND::NT_BV_OR:
        case NODE_KIND::NT_BV_XOR:
        case NODE_KIND::NT_BV_NAND:
        case NODE_KIND::NT_BV_NOR:
        case NODE_KIND::NT_BV_XNOR:
        case NODE_KIND::NT_BV_COMP:
            return dumpChainOp(kind, children);
        // Arithmetic operations
        case NODE_KIND::NT_BV_NEG:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_BV_ADD:
        case NODE_KIND::NT_BV_SUB:
        case NODE_KIND::NT_BV_MUL:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_BV_UDIV:
        case NODE_KIND::NT_BV_SDIV:
        case NODE_KIND::NT_BV_UREM:
        case NODE_KIND::NT_BV_SREM:
        case NODE_KIND::NT_BV_UMOD:
        case NODE_KIND::NT_BV_SMOD:
            return dumpDoubleOp(kind, children[0], children[1]);
        // Arithmetic operations with overflow
        case NODE_KIND::NT_BV_NEGO:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_BV_SADDO:
        case NODE_KIND::NT_BV_UADDO:
        case NODE_KIND::NT_BV_SMULO:
        case NODE_KIND::NT_BV_UMULO:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_BV_SDIVO:
        case NODE_KIND::NT_BV_UDIVO:
        case NODE_KIND::NT_BV_SREMO:
        case NODE_KIND::NT_BV_UREMO:
        case NODE_KIND::NT_BV_SMODO:
        case NODE_KIND::NT_BV_UMODO:
            return dumpDoubleOp(kind, children[0], children[1]);
        // Shift operations
        case NODE_KIND::NT_BV_SHL:
        case NODE_KIND::NT_BV_LSHR:
        case NODE_KIND::NT_BV_ASHR:
            return dumpDoubleOp(kind, children[0], children[1]);
        // Function
        case NODE_KIND::NT_BV_CONCAT:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_BV_EXTRACT:{
            std::string res = "((_ extract " + children[1]->dumpSMTLIB2() + " " + children[2]->dumpSMTLIB2() + ") " + children[0]->dumpSMTLIB2() + ")";
            return res;
        }
        case NODE_KIND::NT_BV_REPEAT:
        case NODE_KIND::NT_BV_ZERO_EXT:
        case NODE_KIND::NT_BV_SIGN_EXT:
        case NODE_KIND::NT_BV_ROTATE_LEFT:
        case NODE_KIND::NT_BV_ROTATE_RIGHT:{
            std::string res = "((_ " + kindToString(kind) + " " + children[1]->dumpSMTLIB2() + ") " + children[0]->dumpSMTLIB2() + ")";
            return res;
        }
        // BITVECTOR COMP
        case NODE_KIND::NT_BV_ULT:
        case NODE_KIND::NT_BV_ULE:
        case NODE_KIND::NT_BV_UGT:
        case NODE_KIND::NT_BV_UGE:
        case NODE_KIND::NT_BV_SLT:
        case NODE_KIND::NT_BV_SLE:
        case NODE_KIND::NT_BV_SGT:
        case NODE_KIND::NT_BV_SGE:
            return dumpDoubleOp(kind, children[0], children[1]);
        // BITVECTOR CONVERSION
        case NODE_KIND::NT_BV_TO_NAT:
        case NODE_KIND::NT_NAT_TO_BV:
            return dumpSingleOp(kind, children[0]);
        // FLOATING POINT COMMON OPERATORS
        case NODE_KIND::NT_FP_ADD:
        case NODE_KIND::NT_FP_SUB:
        case NODE_KIND::NT_FP_MUL:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_FP_DIV:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_FP_ABS:
        case NODE_KIND::NT_FP_NEG:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_FP_REM:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_FP_FMA:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        case NODE_KIND::NT_FP_SQRT:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_FP_MIN:
        case NODE_KIND::NT_FP_MAX:
            return dumpChainOp(kind, children);
        // FLOATING POINT COMP
        case NODE_KIND::NT_FP_LE:
        case NODE_KIND::NT_FP_LT:
        case NODE_KIND::NT_FP_GE:
        case NODE_KIND::NT_FP_GT:
        case NODE_KIND::NT_FP_EQ:
            return dumpDoubleOp(kind, children[0], children[1]);
        // FLOATING POINT CONVERSION
        case NODE_KIND::NT_FP_TO_UBV:
        case NODE_KIND::NT_FP_TO_SBV:
        case NODE_KIND::NT_FP_TO_REAL:
        case NODE_KIND::NT_FP_TO_FP:
            return dumpSingleOp(kind, children[0]);
        // FLOATING POINT PROPERTIES
        case NODE_KIND::NT_FP_IS_NORMAL:
        case NODE_KIND::NT_FP_IS_SUBNORMAL:
        case NODE_KIND::NT_FP_IS_ZERO:
        case NODE_KIND::NT_FP_IS_INF:
        case NODE_KIND::NT_FP_IS_NAN:
        case NODE_KIND::NT_FP_IS_NEG:
        case NODE_KIND::NT_FP_IS_POS:
            return dumpSingleOp(kind, children[0]);
        // ARRAY
        case NODE_KIND::NT_SELECT:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_STORE:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        // STRINGS COMMON OPERATORS
        case NODE_KIND::NT_STR_LEN:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_STR_CONCAT:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_STR_SUBSTR:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        case NODE_KIND::NT_STR_PREFIXOF:
        case NODE_KIND::NT_STR_SUFFIXOF:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_STR_INDEXOF:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        case NODE_KIND::NT_STR_CHARAT: 
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_STR_UPDATE:
        case NODE_KIND::NT_STR_REPLACE:
        case NODE_KIND::NT_STR_REPLACE_ALL:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        case NODE_KIND::NT_STR_TO_LOWER:
        case NODE_KIND::NT_STR_TO_UPPER:
        case NODE_KIND::NT_STR_REV:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_STR_SPLIT:
            return dumpDoubleOp(kind, children[0], children[1]);
        // STRINGS COMP
        case NODE_KIND::NT_STR_LT:
        case NODE_KIND::NT_STR_LE:
        case NODE_KIND::NT_STR_GT:
        case NODE_KIND::NT_STR_GE:
            return dumpDoubleOp(kind, children[0], children[1]);
        // STRINGS PROPERTIES
        case NODE_KIND::NT_STR_IN_REG:
        case NODE_KIND::NT_STR_CONTAINS:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_STR_IS_DIGIT:
            return dumpSingleOp(kind, children[0]);
        // STRINGS CONVERSION
        case NODE_KIND::NT_STR_FROM_INT:
        case NODE_KIND::NT_STR_TO_INT:
        case NODE_KIND::NT_STR_TO_REG:
        case NODE_KIND::NT_STR_TO_CODE:
        case NODE_KIND::NT_STR_FROM_CODE:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_REG_NONE:
            return "re.none";
        case NODE_KIND::NT_REG_ALL:
            return "re.all";
        case NODE_KIND::NT_REG_ALLCHAR:
            return "re.allchar";
        case NODE_KIND::NT_REG_CONCAT:
        case NODE_KIND::NT_REG_UNION:
        case NODE_KIND::NT_REG_INTER:
        case NODE_KIND::NT_REG_DIFF:
            return dumpChainOp(kind, children);
        case NODE_KIND::NT_REG_STAR:
        case NODE_KIND::NT_REG_PLUS:
        case NODE_KIND::NT_REG_OPT:
            return dumpSingleOp(kind, children[0]);
        case NODE_KIND::NT_REG_RANGE:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_REG_REPEAT:
            return dumpDoubleOp(kind, children[0], children[1]);
        case NODE_KIND::NT_REG_LOOP:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        case NODE_KIND::NT_REG_COMPLEMENT:
            return dumpSingleOp(kind, children[0]);
        // STRINGS RE FUNCTIONS
        case NODE_KIND::NT_REPLACE_REG:
        case NODE_KIND::NT_REPLACE_REG_ALL:
        case NODE_KIND::NT_INDEXOF_REG:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        // LET, FROM HERE TODO
        case NODE_KIND::NT_LET:
            return children[0]->dumpSMTLIB2();
        // ITE
        case NODE_KIND::NT_ITE:
            return dumpTripleOp(kind, children[0], children[1], children[2]);
        // QUANTIFIERS
        case NODE_KIND::NT_FORALL:
        case NODE_KIND::NT_EXISTS:
            return dumpQuantOp(kind, children);
        case NODE_KIND::NT_QUANT_VAR:
            return name;
        // FUNC
        case NODE_KIND::NT_FUNC_DEC:{
            return name;
        }; break;
        case NODE_KIND::NT_FUNC_DEF:{
            return name;
        }; break;
        case NODE_KIND::NT_FUNC_PARAM:
            return name;
        case NODE_KIND::NT_FUNC_APPLY:{
            std::string res = "(" + name;
            for(size_t i=1;i<children.size();i++){
                res += " " + children[i]->dumpSMTLIB2();
            }
            res += ")";
            return res;
        }
        default:
            return "UNKNOWN_KIND";
        }
        return res;
    }
    
    std::string DAGNode::dumpFuncDef()   const{
        std::string res = "(define-fun " + name + " (";
        for(size_t i=1;i<children.size();i++){
            if(i==1) res += "(" + children[i]->name +" " + children[i]->getSort()->toString() +")";
            else res += " (" + children[i]->name +" " + children[i]->getSort()->toString() +")";
        }
        res += ") " + children[0]->getSort()->toString() + " ";
        res += children[0]->dumpSMTLIB2() +  ")";
        return res;
    }
    std::string DAGNode::dumpFuncDec()   const{
        std::string res = "(declare-fun " + name + " (";
        for(size_t i=1;i<children.size();i++){
            if(i==1) res += children[i]->getSort()->toString();
            else res += " " + children[i]->getSort()->toString();
        }
        res += ") " + children[0]->getSort()->toString() + ")";
        return res;
    }
}