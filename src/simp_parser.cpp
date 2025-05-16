/* -*- Source -*-
*
* An SMT/OMT Parser (Operator part)
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

#include "parser.h"
std::shared_ptr<DAGNode> Parser::simp_oper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p){
    switch(t){
        // Unary operation - accepts one parameter
        case NODE_KIND::NT_NOT:{
            if(param->isTrue()){
                return mkFalse();
            }
            else{
                // param is false
                return mkTrue();
            }
        }
        case NODE_KIND::NT_NEG:{
            if(p->isCInt()){
                return mkConstInt(-p->toInt());
            }
            else{
                // p is a real number
                return mkConstReal(-p->toReal());
            }
        }
        case NODE_KIND::NT_ABS:{
            if(p->isCInt()){
                Integer i = p->toInt();
                if(i < 0){
                    return mkConstInt(-i);
                }
                else{
                    return p;
                }
            }
            else{
                // p is a real number
                Real r = p->toReal();
                if(r < 0){
                    return mkConstReal(-r);
                }
                else{
                    return p;
                }
            }
        }
        case NODE_KIND::NT_SQRT:{
            if(p->isCInt()){
                Integer i = p->toInt();
                if(i < 0){
                    err_all(p, "Square root of negative integer", line_number);
                    return mkUnknown();
                }
                else{
                    return mkConstInt(sqrt(i));
                }
            }
            else{
                // p is a real number
                Real r = p->toReal();
                if(r < 0){
                    err_all(p, "Square root of negative real number", line_number);
                    return mkUnknown();
                }
                else{
                    return mkConstReal(sqrt(r));
                }
            }
        }
        case NODE_KIND::NT_SAFESQRT:{
            if(p->isCInt()){
                Integer i = p->toInt();
                if(i < 0){
                    return mkConstInt(0);
                }
                else{
                    return mkConstInt(sqrt(i));
                }
            }
            else{
                // p is a real number
                Real r = p->toReal();
                if(r < 0){
                    return mkConstReal(0);
                }
                else{
                    return mkConstReal(sqrt(r));
                }
            }
        }
        case NODE_KIND::NT_CEIL:{
            if(p->isCInt()){
                return p;
            }
            else{
                // p is a real number
                return mkConstReal(ceil(p->toReal()));
            }
        }
        case NODE_KIND::NT_FLOOR:{
            if(p->isCInt()){
                return p;
            }
            else{
                // p is a real number
                return mkConstReal(floor(p->toReal()));
            }
        }
        case NODE_KIND::NT_ROUND:{
            if(p->isCInt()){
                return p;
            }
            else{
                // p is a real number
                return mkConstReal(round(p->toReal()));
            }
        }
        case NODE_KIND::NT_EXP:{
            if(p->isCInt()){
                return mkConstReal(exp(p->toReal()));
            }
            else{
                // p is a real number
                return mkConstReal(exp(p->toReal()));
            }
        }
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
        case NODE_KIND::NT_NAT_TO_BV:
        case NODE_KIND::NT_BV_TO_INT:
        case NODE_KIND::NT_INT_TO_BV:
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
    }
}