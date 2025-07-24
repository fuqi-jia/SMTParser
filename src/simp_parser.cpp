/* -*- Source -*-
*
* An SMT/OMT Parser (simplification part)
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
#include "timing.h"

namespace SMTParser{
    void precision_warning(const std::string& op){
        std::cerr << "Precision warning: " << op << " will use double precision" << std::endl;
    }
    std::shared_ptr<DAGNode> Parser::simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> p){
        TIME_FUNC();
        switch(t){
            // Unary operation - accepts one parameter
            case NODE_KIND::NT_NOT:{
                if(p->isTrue()){
                    return mkFalse();
                }
                else if(p->isFalse()){
                    return mkTrue();
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_NEG:{
                if(p->isCInt()){
                    return mkConstInt(
                        -toInt(p)
                    );
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(
                        -toReal(p)
                    );
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_ABS:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(i < 0){
                        return mkConstInt(-i);
                    }
                    else{
                        return p;
                    }
                }
                else if(p->isCReal()){
                    // p is a real number
                    Real r = toReal(p);
                    if(r < 0){
                        return mkConstReal(-r);
                    }
                    else{
                        return p;
                    }
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_SQRT:{
                // use floating point to approximate
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sqrt());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sqrt());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SAFESQRT:{
                // use floating point to approximate
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).safeSqrt());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).safeSqrt());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_CEIL:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(toReal(p).ceil());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_FLOOR:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(toReal(p).floor());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_ROUND:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(toReal(p).round());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_EXP:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).exp());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).exp());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LN:{
                // ln(x) = ln(e^ln(x)) = ln(e) + ln(x)
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).ln());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).ln());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LG:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).lg());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).lg());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LB:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).lb());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).lb());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SIN:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sin());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sin());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_COS:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cos());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cos());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SEC:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sec());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sec());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_CSC:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).csc());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).csc());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_TAN:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).tan());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).tan());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_COT:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cot());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cot());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ASIN:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asin());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asin());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACOS:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acos());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acos());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ASEC:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asec());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asec());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACSC:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acsc());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acsc());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ATAN:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).atan());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).atan());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACOT:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acot());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acot());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SINH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sinh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sinh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_COSH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cosh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).cosh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_TANH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).tanh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).tanh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SECH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sech());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).sech());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_CSCH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).csch());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).csch());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_COTH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).coth());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).coth());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ASINH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asinh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asinh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACOSH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acosh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acosh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ATANH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).atanh());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).atanh());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ASECH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asech());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).asech());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACSCH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acsch());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acsch());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ACOTH:{
                if(p->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acoth());
                    }
                }
                else if(p->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(p).acoth());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_TO_INT:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    return mkConstReal(toReal(p).floor());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_TO_REAL:{
                if(p->isCInt()){
                    return mkConstReal(toInt(p));
                }
                else if(p->isCReal()){
                    return p;
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_IS_INT:{
                if(p->isCInt()){
                    return mkTrue();
                }
                else if(p->isCReal()){
                    return mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_IS_PRIME:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(MathUtils::isPrime(i)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else{
                    err_all(p, "Prime check on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_IS_EVEN:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(MathUtils::isEven(i)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else{
                    err_all(p, "Even check on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_IS_ODD:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(MathUtils::isOdd(i)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else{
                    err_all(p, "Odd check on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_FACT:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(i < 0){
                        err_all(p, "Factorial of negative integer", line_number);
                        return mkUnknown();
                    }
                    else if(i == 0){
                        return mkConstInt(1);
                    }
                    else{
                        return mkConstInt(MathUtils::factorial(i));
                    }
                }
                else{
                    err_all(p, "Factorial on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_NOT:{
                if(p->isCBV()){
                    return mkConstBv(BitVectorUtils::bvNot(p->toString()), p->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_NEG:{
                if(p->isCBV()){
                    return mkConstBv(BitVectorUtils::bvNeg(p->toString()), p->getSort()->getBitWidth());
                }
                return mkUnknown();
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
            case NODE_KIND::NT_FP_TO_UBV:
            case NODE_KIND::NT_FP_TO_SBV:
            case NODE_KIND::NT_FP_TO_REAL:
            case NODE_KIND::NT_FP_TO_FP:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_LEN:{
                if(p->isCStr()){
                    return mkConstInt(p->toString().size());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_TO_LOWER:{
                if(p->isCStr()){
                    return mkConstStr(StringUtils::strToLower(p->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_TO_UPPER:{
                if(p->isCStr()){
                    return mkConstStr(StringUtils::strToUpper(p->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_REV:{
                if(p->isCStr()){
                    return mkConstStr(StringUtils::strRev(p->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_IS_DIGIT:{
                if(p->isCStr()){
                    return TypeChecker::isInt(p->toString()) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_FROM_INT:{
                if(p->isCInt()){
                    return mkConstStr(p->toString());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_TO_INT:{
                if(p->isCStr()){
                    if(TypeChecker::isInt(p->toString())){
                        return mkConstInt(stoi(p->toString()));
                    }
                    else{
                        err_all(p, "String to int on non-integer", line_number);
                        return mkUnknown();
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_TO_CODE:{
                if(p->isCStr()){
                    if(p->toString().size() == 1){
                        return mkConstInt(static_cast<int>(p->toString()[0]));
                    }
                    else{
                        err_all(p, "String to code on non-single character string", line_number);
                        return mkUnknown();
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_FROM_CODE:{
                if(p->isCInt()){
                    if(toInt(p) >= 0 && toInt(p) <= 127){
                        return mkConstStr(std::string(1, static_cast<char>(toInt(p).toULong())));
                    }
                    else{
                        err_all(p, "String from code on non-ASCII character", line_number);
                        return mkUnknown();
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_REG_STAR:
            case NODE_KIND::NT_REG_PLUS:
            case NODE_KIND::NT_REG_OPT:
            case NODE_KIND::NT_REG_COMPLEMENT:
            case NODE_KIND::NT_STR_TO_REG:{
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_TO_NAT:{
                if(p->isCBV()){
                    return mkConstInt(BitVectorUtils::bvToNat(p->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_TO_INT:{
                if(p->isCBV()){
                    return mkConstInt(BitVectorUtils::bvToInt(p->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_POW2:{
                if(p->isCInt()){
                    return mkConstInt(MathUtils::pow(2, toInt(p)));
                }
                else if(p->isCReal()){
                    return mkUnknown();
                }
                return mkUnknown();
            }
            
            // Multi-parameter operation - accepts arbitrary number of parameters
            // if only accepts one parameter, just return it
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:
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
            case NODE_KIND::NT_REG_DIFF:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN: {
                return p;
            }
            default:
                return mkUnknown();
        }
        return mkUnknown();
    }
    std::shared_ptr<DAGNode> Parser::simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        switch(t){
            // Binary operation - accepts two parameters
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) == toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt())){
                    if(toReal(l) == toReal(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(l->isCBV() && r->isCBV()){
                    if(l->toString() == r->toString()){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(l->isCStr() && r->isCStr()){
                    if(l->toString() == r->toString()){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_POW:{
                if(l->isCInt() && r->isCInt()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(l).pow(toReal(r)));
                    }
                }
                else if(l->isCReal() && r->isCReal()){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(l).pow(toReal(r)));
                    }
                }
                else if((l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(l).pow(toReal(r)));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_DIV_INT:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) / toInt(r));
                }
                else if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt()) || (l->isCInt() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        return mkConstInt((toReal(l) / toReal(r)).floor().toInt());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_DIV_REAL:{
                if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt()) || (l->isCInt() && r->isCInt())){
                    if(options->keep_division_if_not_divisible){
                        if((toReal(l) / toReal(r)).isInteger()){
                            return mkConstInt((toReal(l) / toReal(r)).floor().toInt());
                        }
                        else{
                            // keep original representation
                        }
                    }
                    else if(getEvaluateUseFloating()){
                        return mkConstReal(toReal(l) / toReal(r));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_MOD:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) % toInt(r));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LOG:{
                if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt()) || (l->isCInt() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        // log_r(l)
                        return mkConstReal(toReal(l).log(toReal(r)));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ATAN2:{
                if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt()) || (l->isCInt() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        return mkConstReal(Real::atan2(toReal(l), toReal(r)));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LE:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) <= toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt())){
                    if(toReal(l) <= toReal(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LT:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) < toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        if(toReal(l) < toReal(r)){
                            return mkTrue();
                        }
                        else{
                            return mkFalse();
                        }
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_GE:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) >= toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if((l->isCReal() && r->isCReal()) || (l->isCInt() && r->isCReal()) || (l->isCReal() && r->isCInt())){
                    if(getEvaluateUseFloating()){
                        if(toReal(l) >= toReal(r)){
                            return mkTrue();
                        }
                        else{
                            return mkFalse();
                        }
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_GT:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) > toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(l->isCReal() && r->isCReal()){
                    if(getEvaluateUseFloating()){
                        if(toReal(l) > toReal(r)){
                            return mkTrue();
                        }
                        else{
                            return mkFalse();
                        }
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_IS_DIVISIBLE:{
                if(l->isCInt() && r->isCInt()){
                    return toInt(l) % toInt(r) == 0 ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Is divisible on non-integer", line_number);
                    err_all(r, "Is divisible on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_GCD:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(MathUtils::gcd(toInt(l), toInt(r)));
                }
                else{
                    err_all(l, "GCD on non-integer", line_number);
                    err_all(r, "GCD on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_LCM:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(MathUtils::lcm(toInt(l), toInt(r)));
                }
                else{
                    err_all(l, "LCM on non-integer", line_number);
                    err_all(r, "LCM on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_UDIV:{
                // division by zero evaluates to all ones.
                if(r->isCBV() && isZero(r)){
                    return mkConstBv("#b" + std::string(l->getSort()->getBitWidth(), '1'), l->getSort()->getBitWidth());
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvUdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SDIV:{            
                // bvsdiv by zero evaluates to all ones if it's positive, otherwise 1.
                if(r->isCBV() && isZero(r)){
                    if(l->isCBV() && Integer(BitVectorUtils::bvToInt(l->toString())) >= 0){
                        return mkConstBv("#b" + std::string(l->getSort()->getBitWidth(), '1'), l->getSort()->getBitWidth());
                    }
                    else{
                        return mkConstBv("#b" + std::string(l->getSort()->getBitWidth() - 1, '0') + "1", l->getSort()->getBitWidth());
                    }
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvSdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_UREM:{
                // remainder by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvUrem(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SREM:{
                // bvsrem by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvSrem(l->toString(), r->toString()), r->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_UMOD:{
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvUmod(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SMOD:{
                // bvsmod by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvSmod(l->toString(), r->toString()), r->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SDIVO:
            case NODE_KIND::NT_BV_UDIVO:
            case NODE_KIND::NT_BV_SREMO:
            case NODE_KIND::NT_BV_UREMO:
            case NODE_KIND::NT_BV_SMODO:
            case NODE_KIND::NT_BV_UMODO:{
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SHL:{
                // shift amount is zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvShl(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_LSHR:{
                // shift amount is zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvLshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_ASHR:{
                // shift amount is zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvAshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_ULT:
            case NODE_KIND::NT_BV_ULE:
            case NODE_KIND::NT_BV_UGT:
            case NODE_KIND::NT_BV_UGE:
            case NODE_KIND::NT_BV_SLT:
            case NODE_KIND::NT_BV_SLE:
            case NODE_KIND::NT_BV_SGT:
            case NODE_KIND::NT_BV_SGE:{
                if(l->isCBV() && r->isCBV()){
                    return BitVectorUtils::bvComp(l->toString(), r->toString(), t) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_NAT_TO_BV:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstBv(BitVectorUtils::natToBv(toInt(l), toInt(r)), toInt(r).toULong());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_INT_TO_BV:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstBv(BitVectorUtils::intToBv(toInt(l), toInt(r)), toInt(r).toULong());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_FP_DIV:
            case NODE_KIND::NT_FP_REM:
            case NODE_KIND::NT_FP_LE:
            case NODE_KIND::NT_FP_LT:
            case NODE_KIND::NT_FP_GE:
            case NODE_KIND::NT_FP_GT:
            case NODE_KIND::NT_FP_EQ:
            case NODE_KIND::NT_FP_NE:
            case NODE_KIND::NT_SELECT:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_PREFIXOF:{
                if(l->isCStr() && r->isCStr()){
                    return StringUtils::strPrefixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_SUFFIXOF:{
                if(l->isCStr() && r->isCStr()){
                    return StringUtils::strSuffixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_CHARAT:{
                if(l->isCStr() && r->isCInt()){
                    return mkConstStr(StringUtils::strCharAt(l->toString(), toInt(r)));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_SPLIT:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_LT:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() < r->toString() ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_LE:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() <= r->toString() ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_GT:{
                if(l->isCStr() && r->isCStr()){ 
                    return l->toString() > r->toString() ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_GE:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() >= r->toString() ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_CONTAINS:{
                if(l->isCStr() && r->isCStr()){
                    return StringUtils::strContains(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_IN_REG:
            case NODE_KIND::NT_REG_RANGE:
            case NODE_KIND::NT_REG_REPEAT:{
                return mkUnknown();
            }
                
            // Multi-parameter operation - accepts arbitrary number of parameters
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) == toInt(r)){
                        return mkFalse();
                    }
                    else{
                        return mkTrue();
                    }
                }
                else if(l->isCReal() && r->isCReal()){
                    if(toReal(l) == toReal(r)){
                        return mkFalse();
                    }
                    else{
                        return mkTrue();
                    }
                }
                else if(l->isCBV() && r->isCBV()){
                    return l->toString() == r->toString() ? mkFalse() : mkTrue();
                }
                else if(l->isCStr() && r->isCStr()){
                    return l->toString() == r->toString() ? mkFalse() : mkTrue();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_AND:{
                if(l->isFalse() || r->isFalse()){
                    return mkFalse();
                }
                else if(l->isTrue() || r->isTrue()){
                    return mkTrue();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_OR:{
                if(l->isTrue() || r->isTrue()){
                    return mkTrue();
                }
                else if(l->isFalse() && r->isFalse()){
                    return mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_IMPLIES:{
                if(l->isTrue() && r->isFalse()){
                    return mkFalse();
                }
                else if(l->isFalse() || r->isTrue()){
                    return mkTrue();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_XOR:{
                if(l->isTrue() && r->isTrue()){
                    return mkFalse();
                }
                else if(l->isFalse() && r->isFalse()){
                    return mkFalse();
                }
                else if(l->isTrue() && r->isFalse()){
                    return mkTrue();
                }
                else if(l->isFalse() && r->isTrue()){
                    return mkTrue();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ADD:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) + toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) + toReal(r));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_MUL:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) * toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) * toReal(r));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_IAND:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) & toInt(r));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_SUB:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) - toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) - toReal(r));
                }
                else if(isZero(l)){
                    return mkNeg(r);
                }
                else if(isZero(r)){
                    return l;
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_AND:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvAnd(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_OR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvOr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_XOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvXor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_NAND:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvNand(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_NOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvNor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_XNOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvXnor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_COMP:{
                if(l->isCBV() && r->isCBV()){
                    return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_COMP) ? mkTrue() : mkFalse();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_ADD:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvAdd(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SUB:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvSub(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_MUL:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvMul(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_SADDO:
            case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SMULO:
            case NODE_KIND::NT_BV_UMULO:{
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_CONCAT:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(BitVectorUtils::bvConcat(l->toString(), r->toString()), l->getSort()->getBitWidth() + r->getSort()->getBitWidth());
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_CONCAT:{
                if(l->isCStr() && r->isCStr()){
                    std::string l_str = l->toString();
                    std::string r_str = r->toString();
                    if(l_str.back() == '\"' && r_str.front() == '\"'){
                        return mkConstStr(l_str.substr(0, l_str.size() - 1) + r_str.substr(1));
                    }
                    else{
                        return mkConstStr(l->toString() + r->toString());
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_MAX:{
                std::shared_ptr<Sort> sort = getSort({l, r});
                if(l->isConst() && r->isConst()){
                    if(sort->isReal()){
                        return mkConstReal(std::max(toReal(l), toReal(r)));
                    }
                    else if(sort->isInt()){
                        return mkConstInt(std::max(toInt(l), toInt(r)));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_MIN:{
                std::shared_ptr<Sort> sort = getSort({l, r});
                if(l->isConst() && r->isConst()){
                    if(sort->isReal()){
                        return mkConstReal(std::min(toReal(l), toReal(r)));
                    }
                    else if(sort->isInt()){
                        return mkConstInt(std::min(toInt(l), toInt(r)));
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX:
            case NODE_KIND::NT_REG_CONCAT:
            case NODE_KIND::NT_REG_UNION:
            case NODE_KIND::NT_REG_INTER:
            case NODE_KIND::NT_REG_DIFF: 
            default:
                return mkUnknown();
        }
        return mkUnknown();
    }
    std::shared_ptr<DAGNode> Parser::simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        switch(t){
            // Ternary operation - accepts three parameters
            case NODE_KIND::NT_ITE:{
                if(l->isTrue()){
                    return m;
                }
                else if(l->isFalse()){
                    return r;
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_FP_FMA:
            case NODE_KIND::NT_STORE:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_SUBSTR:{
                if(l->isCStr() && m->isCInt() && r->isCInt()){
                    return mkConstStr(StringUtils::strSubstr(l->toString(), toInt(m), toInt(r)));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_INDEXOF:{
                if(l->isCStr() && m->isCStr() && r->isCInt()){
                    return mkConstInt(StringUtils::strIndexof(l->toString(), m->toString(), toInt(r)));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_UPDATE:{
                if(l->isCStr() && m->isCInt() && r->isCStr()){
                    return mkConstStr(StringUtils::strUpdate(l->toString(), toInt(m), r->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_REPLACE:{
                if(l->isCStr() && m->isCStr() && r->isCStr()){
                    return mkConstStr(StringUtils::strReplace(l->toString(), m->toString(), r->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_REPLACE_ALL:{
                if(l->isCStr() && m->isCStr() && r->isCStr()){
                    return mkConstStr(StringUtils::strReplaceAll(l->toString(), m->toString(), r->toString()));
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_REG_LOOP:
            case NODE_KIND::NT_STR_REPLACE_REG:
            case NODE_KIND::NT_STR_REPLACE_REG_ALL:
            case NODE_KIND::NT_STR_INDEXOF_REG:{
                return mkUnknown();
            }
            // Special processing operation
            case NODE_KIND::NT_BV_EXTRACT:{
                if(l->isCBV() && m->isCInt() && r->isCInt()){
                    Integer size = (toInt(m) - toInt(r) + 1);
                    return mkConstBv(BitVectorUtils::bvExtract(l->toString(), toInt(m), toInt(r)), size.toULong());
                }
                return mkUnknown();
            }

            // Multi-parameter operation - accepts arbitrary number of parameters
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:{
                if(l->isCInt() && m->isCInt() && r->isCInt()){
                    if(toInt(l) == toInt(m) && toInt(m) == toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(l->isCReal() && m->isCReal() && r->isCReal()){
                    if(toReal(l) == toReal(m) && toReal(m) == toReal(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(simp_oper(NODE_KIND::NT_EQ, l, m)->isTrue() && simp_oper(NODE_KIND::NT_EQ, m, r)->isTrue()){
                    return mkTrue();
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:{
                if(l->isCInt() && m->isCInt() && r->isCInt()){
                    if(toInt(l) != toInt(m) && toInt(l) != toInt(r) && toInt(m) != toInt(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(l->isCReal() && m->isCReal() && r->isCReal()){
                    if(toReal(l) != toReal(m) && toReal(l) != toReal(r) && toReal(m) != toReal(r)){
                        return mkTrue();
                    }
                    else{
                        return mkFalse();
                    }
                }
                else if(simp_oper(NODE_KIND::NT_DISTINCT, l, m)->isTrue() && simp_oper(NODE_KIND::NT_DISTINCT, l, r)->isTrue() && simp_oper(NODE_KIND::NT_DISTINCT, m, r)->isTrue()){
                    return mkTrue();
                }
                return mkUnknown();
            }
            // convert to multi-pairs using {{l, m}, r}
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
            case NODE_KIND::NT_BV_CONCAT:
            case NODE_KIND::NT_STR_CONCAT:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:{
                // convert to multi-pairs using {{l, m}, r}
                std::shared_ptr<DAGNode> result = l;
                result = simp_oper(t, result, m);
                result = simp_oper(t, result, r);
                return result;
            }
            case NODE_KIND::NT_BV_SADDO:
            case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SMULO:
            case NODE_KIND::NT_BV_UMULO:{
                return mkUnknown();
            }
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX:
            case NODE_KIND::NT_REG_CONCAT:
            case NODE_KIND::NT_REG_UNION:
            case NODE_KIND::NT_REG_INTER:
            case NODE_KIND::NT_REG_DIFF: 
            default:
                return mkUnknown();
        }
        return mkUnknown();
    }
    std::shared_ptr<DAGNode> Parser::simp_oper(const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p){
        switch(t){
            // Multi-parameter operation - accepts arbitrary number of parameters
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:{
                // convert to multi-pairs using {{l, m}, r}
                // find the first constant parameter
                int first_const_idx = -1;
                for(size_t i=0;i<p.size();i++){
                    if(p[i]->isConst()){
                        first_const_idx = (int)i;
                        break;
                    }
                }
                if(first_const_idx == -1){
                    // all parameters are non-constants
                    return mkUnknown();
                }
                condAssert(first_const_idx != -1, "the first constant parameter index is -1");
                std::vector<std::shared_ptr<DAGNode>> params;
                for(size_t i=0;i<p.size();i++){
                    if(i == (size_t)first_const_idx){
                        continue;
                    }
                    auto child_result = simp_oper(t, p[first_const_idx], p[i]);
                    if(child_result->isUnknown()){
                        params.push_back(p[i]);
                    }
                    else if(child_result->isTrue()){
                        continue;
                    }
                    else if(child_result->isFalse()){
                        return mkFalse();
                    }
                }
                if(params.size() == 0){
                    // all parameters are constants and all equivalent
                    return mkTrue();
                }
                else if(params.size() == 1){
                    // one parameter is constant and the other parameter is non-constant
                    return simp_oper(t, params[0], p[first_const_idx]);
                }
                else{
                    if(params.size() == p.size() - 1){
                        // only p[first_const_idx] is constant, while all other parameters are non-constants
                        return mkUnknown();
                    }
                    else{
                        // multiple parameters are constants and all equivalent
                        params.emplace_back(p[first_const_idx]); // add the constant parameter to the end of the vector
                        condAssert(params.size() < p.size(), "the size of params is greater than or equal to the size of p, which may cause infinite loop");
                        return simp_oper(t, params);
                    }
                }
            }
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:{
                // convert to multi-pairs using {{l, m}, r}
                bool is_unknown = false;
                for(size_t i=0;i<p.size();i++){
                    for(size_t j=i+1;j<p.size();j++){
                        auto child_result = simp_oper(t, p[i], p[j]);
                        if(child_result->isUnknown()){
                            is_unknown = true;
                        }
                        else if(child_result->isFalse()){
                            return mkFalse();
                        }
                    }
                }
                if(is_unknown){
                    return mkUnknown();
                }
                else{
                    return mkTrue();
                }
            }
            case NODE_KIND::NT_IMPLIES:{
                // -p[0] -p[1] -p[2] -p[3] ... p[n]
                bool is_constant = true;
                for(size_t i=0;i<p.size();i++){
                    if(i != p.size()-1){
                        if(p[i]->isFalse()){
                            return mkTrue();
                        }
                        if(!p[i]->isTrue()){
                            is_constant = false;
                        }
                    }
                    else{
                        if(p[i]->isTrue()){
                            return mkTrue();
                        }
                        if(!p[i]->isFalse()){
                            is_constant = false;
                        }
                    }
                }
                if(is_constant){
                    return mkFalse();
                }
                else{
                    return mkUnknown();
                }
            }
            // convert to multi-pairs using {{l, m}, r}
            case NODE_KIND::NT_AND:
            case NODE_KIND::NT_OR:
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
            case NODE_KIND::NT_BV_CONCAT:
            case NODE_KIND::NT_STR_CONCAT:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:{
                // convert to multi-pairs using {{l, m}, r}
                std::shared_ptr<DAGNode> result = p[0];
                for(size_t i=1;i<p.size();i++){
                    result = simp_oper(t, result, p[i]);
                    if(result->isUnknown()){
                        return mkUnknown();
                    }
                }
                return result;
            }
            case NODE_KIND::NT_BV_SADDO:
            case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SMULO:
            case NODE_KIND::NT_BV_UMULO:{
                return mkUnknown();
            }
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX:
            case NODE_KIND::NT_REG_CONCAT:
            case NODE_KIND::NT_REG_UNION:
            case NODE_KIND::NT_REG_INTER:
            case NODE_KIND::NT_REG_DIFF: 
            default:
                return mkUnknown();
        }
        return mkUnknown();
    }
}
