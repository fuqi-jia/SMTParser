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

namespace SMTLIBParser{
    void precision_warning(const std::string& op){
        std::cerr << "Precision warning: " << op << " will use double precision" << std::endl;
    }
    std::shared_ptr<DAGNode> Parser::simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> p){
        switch(t){
            // Unary operation - accepts one parameter
            case NODE_KIND::NT_NOT:{
                if(p->isTrue()){
                    return mkFalse();
                }
                else{
                    // p is false
                    return mkTrue();
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
                    err_all(p, "Negation on non-integer or non-real", line_number);
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
                    err_all(p, "Absolute value on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_SQRT:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(i < 0){
                        err_all(p, "Square root of negative integer", line_number);
                        return mkUnknown();
                    }
                    else{
                        return mkConstReal(sqrt(i));
                    }
                }
                else if(p->isCReal()){
                    // p is a real number
                    Real r = toReal(p);
                    if(r < 0){
                        err_all(p, "Square root of negative real number", line_number);
                        return mkUnknown();
                    }
                    else{
                        return mkConstReal(sqrt(r));
                    }
                }
                else{
                    err_all(p, "Square root on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_SAFESQRT:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(i < 0){
                        return mkConstReal(0);
                    }
                    else{
                        return mkConstReal(sqrt(i));
                    }
                }
                else if(p->isCReal()){
                    // p is a real number
                    Real r = toReal(p);
                    if(r < 0){
                        return mkConstReal(0);
                    }
                    else{
                        return mkConstReal(sqrt(r));
                    }
                }
                else{
                    err_all(p, "Safe square root on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_CEIL:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(ceil(toReal(p)));
                }
                else{
                    err_all(p, "Ceiling on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_FLOOR:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(floor(toReal(p)));
                }
                else{
                    err_all(p, "Floor on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_ROUND:{
                if(p->isCInt()){
                    return p;
                }
                else if(p->isCReal()){
                    // p is a real number
                    return mkConstReal(round(toReal(p)));
                }
                else{
                    err_all(p, "Round on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_EXP:{
                if(p->isCInt()){
                    if(toInt(p) == 0){
                        return mkConstReal(1.0);
                    }
                }
                else if(p->isCReal()){
                    if(toReal(p) == 0.0){
                        return mkConstReal(1.0);
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LN:{
                // ln(x) = ln(e^ln(x)) = ln(e) + ln(x)
                if(p->isCInt()){
                    if(toInt(p) <= 0){
                        err_all(p, "Natural logarithm of non-positive integer", line_number);
                        return mkUnknown();
                    }
                    else if(toInt(p) == 1){
                        return mkConstReal(0.0);
                    }
                }
                else if(p->isCReal()){
                    if(toReal(p) <= 0.0){
                        err_all(p, "Natural logarithm of non-positive real number", line_number);
                        return mkUnknown();
                    }
                    else if(toReal(p) == 1.0){
                        return mkConstReal(0.0);
                    }
                    else if(p->isE()){
                        return mkConstReal(1.0);
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LG:{
                if(p->isCInt()){
                    if(toInt(p) <= 0){
                        return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
                    }
                    else if(toInt(p) == 1){
                        return mkConstReal(0.0);
                    }
                    else if(toInt(p) == 10){
                        return mkConstReal(1.0);
                    }
                    else if(toInt(p) == 100){
                        return mkConstReal(2.0);
                    }
                    else if(toInt(p) == 1000){
                        return mkConstReal(3.0);
                    }
                    else if(toInt(p) == 10000){
                        return mkConstReal(4.0);
                    }
                    else if(toInt(p) == 100000){
                        return mkConstReal(5.0);
                    }
                    else if(toInt(p) == 1000000){
                        return mkConstReal(6.0);
                    }
                    else if(toInt(p) == 10000000){
                        return mkConstReal(7.0);
                    }
                    else if(toInt(p) == 100000000){
                        return mkConstReal(8.0);
                    }
                    else if(toInt(p) == 1000000000){
                        return mkConstReal(9.0);
                    }
                    else if(toInt(p) == 10000000000){
                        return mkConstReal(10.0);
                    }
                    // ... ...
                }
                else if(p->isCReal()){
                    if(toReal(p) <= 0.0){
                        return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
                    }
                    else if(toReal(p) == 1.0){
                        return mkConstReal(0.0);
                    }
                    else if(toReal(p) == 10.0){
                        return mkConstReal(1.0);
                    }
                    else if(toReal(p) == 100.0){
                        return mkConstReal(2.0);
                    }
                    else if(toReal(p) == 1000.0){
                        return mkConstReal(3.0);
                    }
                    else if(toReal(p) == 10000.0){
                        return mkConstReal(4.0);
                    }
                    else if(toReal(p) == 100000.0){
                        return mkConstReal(5.0);
                    }
                    else if(toReal(p) == 1000000.0){
                        return mkConstReal(6.0);
                    }
                    else if(toReal(p) == 10000000.0){
                        return mkConstReal(7.0);
                    }
                    else if(toReal(p) == 100000000.0){
                        return mkConstReal(8.0);
                    }
                    else if(toReal(p) == 1000000000.0){
                        return mkConstReal(9.0);
                    }
                    else if(toReal(p) == 10000000000.0){
                        return mkConstReal(10.0);
                    }
                    // ... ...
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_LB:{
                if(p->isCInt()){
                    if(toInt(p) <= 0){
                        return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
                    }
                    else if(toInt(p) == 1){
                        return mkConstReal(0.0);
                    }
                    else if(toInt(p) == 2){
                        return mkConstReal(1.0);
                    }
                    else if(toInt(p) == 4){
                        return mkConstReal(2.0);
                    }
                    else if(toInt(p) == 8){
                        return mkConstReal(3.0);
                    }
                    else if(toInt(p) == 16){
                        return mkConstReal(4.0);
                    }
                    else if(toInt(p) == 32){
                        return mkConstReal(5.0);
                    }
                    else if(toInt(p) == 64){
                        return mkConstReal(6.0);
                    }
                    else if(toInt(p) == 128){
                        return mkConstReal(7.0);
                    }
                    else if(toInt(p) == 256){
                        return mkConstReal(8.0);
                    }
                    else if(toInt(p) == 512){
                        return mkConstReal(9.0);
                    }
                    else if(toInt(p) == 1024){
                        return mkConstReal(10.0);
                    }
                }
                else if(p->isCReal()){
                    if(toReal(p) <= 0.0){
                        return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
                    }
                    else if(toReal(p) == 1.0){
                        return mkConstReal(0.0);
                    }
                    else if(toReal(p) == 2.0){
                        return mkConstReal(1.0);
                    }
                    else if(toReal(p) == 4.0){
                        return mkConstReal(2.0);
                    }
                    else if(toReal(p) == 8.0){
                        return mkConstReal(3.0);
                    }
                    else if(toReal(p) == 16.0){
                        return mkConstReal(4.0);
                    }
                    else if(toReal(p) == 32.0){
                        return mkConstReal(5.0);
                    }
                    else if(toReal(p) == 64.0){
                        return mkConstReal(6.0);
                    }
                    else if(toReal(p) == 128.0){
                        return mkConstReal(7.0);
                    }
                    else if(toReal(p) == 256.0){
                        return mkConstReal(8.0);
                    }
                    else if(toReal(p) == 512.0){
                        return mkConstReal(9.0);
                    }
                    else if(toReal(p) == 1024.0){
                        return mkConstReal(10.0);
                    }
                }
                return mkUnknown();
            }
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
            case NODE_KIND::NT_ACOTH:{
                return mkUnknown();
            }
            case NODE_KIND::NT_TO_INT:{
                if(p->isCInt()){
                    return p;
                }
                else{
                    return mkConstInt(floor(toReal(p)));
                }
            }
            case NODE_KIND::NT_TO_REAL:{
                if(p->isCInt()){
                    return mkConstReal(toInt(p));
                }
                else{
                    return p;
                }
            }
            case NODE_KIND::NT_IS_INT:{
                if(p->isCInt()){
                    return mkTrue();
                }
                else{
                    return mkFalse();
                }
            }
            case NODE_KIND::NT_IS_PRIME:{
                if(p->isCInt()){
                    Integer i = toInt(p);
                    if(isPrime(i)){
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
                    if(isEven(i)){
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
                    if(isOdd(i)){
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
                        return mkConstInt(factorial(i));
                    }
                }
                else{
                    err_all(p, "Factorial on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_NOT:{
                if(p->isCBV()){
                    return mkConstBv(bvNot(p->toString()), p->getSort()->getBitWidth());
                }
                else{
                    err_all(p, "Bitwise NOT on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_NEG:{
                if(p->isCBV()){
                    return mkConstBv(bvNeg(p->toString()), p->getSort()->getBitWidth());
                }
                else{
                    err_all(p, "Bitwise NEG on non-bitvector", line_number);
                    return mkUnknown();
                }
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
                else{
                    err_all(p, "String length on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_TO_LOWER:{
                if(p->isCStr()){
                    return mkConstStr(strToLower(p->toString()));
                }
                else{
                    err_all(p, "String to lower on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_TO_UPPER:{
                if(p->isCStr()){
                    return mkConstStr(strToUpper(p->toString()));
                }
                else{
                    err_all(p, "String to upper on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_REV:{
                if(p->isCStr()){
                    return mkConstStr(strRev(p->toString()));
                }
                else{
                    err_all(p, "String reverse on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_IS_DIGIT:{
                if(p->isCStr()){
                    return isIntUtil(p->toString()) ? mkTrue() : mkFalse();
                }
                else{
                    err_all(p, "String is digit on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_FROM_INT:{
                if(p->isCInt()){
                    return mkConstStr(p->toString());
                }
                else{
                    err_all(p, "String from int on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_TO_INT:{
                if(p->isCStr()){
                    if(isIntUtil(p->toString())){
                        return mkConstInt(stoi(p->toString()));
                    }
                    else{
                        err_all(p, "String to int on non-integer", line_number);
                        return mkUnknown();
                    }
                }
                else{
                    err_all(p, "String to int on non-string", line_number);
                    return mkUnknown();
                }
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
                else{
                    err_all(p, "String to code on non-string", line_number);
                    return mkUnknown();
                }
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
                else{
                    err_all(p, "String from code on non-integer", line_number);
                    return mkUnknown();
                }
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
                    return mkConstInt(bvToNat(p->toString()));
                }
                else{
                    err_all(p, "Bitvector to natural on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_TO_INT:{
                if(p->isCBV()){
                    return mkConstInt(bvToInt(p->toString()));
                }
                else{
                    err_all(p, "Bitvector to integer on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_POW2:{
                if(p->isCInt()){
                    return mkConstInt(pow(2, toInt(p)));
                }
                else if(p->isCReal()){
                    return mkUnknown();
                }
                else{
                    err_all(p, "Pow2 on non-integer or non-real", line_number);
                    return mkUnknown();
                }
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
            case NODE_KIND::NT_REG_DIFF: {
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
                if(l->toString() == r->toString()){
                    return mkTrue();
                }
                else{
                    return mkFalse();
                }
            }
            case NODE_KIND::NT_POW:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(pow(toInt(l), toInt(r)));
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_DIV_INT:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) / toInt(r));
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_DIV_REAL:{
                if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) / toReal(r));
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_MOD:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) % toInt(r));
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_LOG:{
                if(l->isCInt() && r->isCInt()){
                    if(toInt(l) <= 0 || toInt(r) <= 0){
                        return l->isErr()?l:r;
                    }
                    else if(toInt(l) == 1){
                        return l->isErr()?l:r;
                    }
                    else if(toInt(r) == 1){
                        return mkConstReal(0.0);
                    }
                }
                else if(l->isCReal() && r->isCReal()){
                    if(toReal(l) <= 0.0 || toReal(r) <= 0.0){
                        return l->isErr()?l:r;
                    }
                    else if(toReal(l) == 1.0){
                        return l->isErr()?l:r;
                    }
                    else if(toReal(r) == 1.0){
                        return mkConstReal(0.0);
                    }
                }
                return mkUnknown();
            }
            case NODE_KIND::NT_ATAN2:{
                return mkUnknown();
            }
            case NODE_KIND::NT_LE:{
                if(l->isCInt() && r->isCInt()){
                    return toInt(l) <= toInt(r) ? mkTrue() : mkFalse();
                }
                else if(l->isCReal() && r->isCReal()){
                    return toReal(l) <= toReal(r) ? mkTrue() : mkFalse();
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_LT:{
                if(l->isCInt() && r->isCInt()){
                    return toInt(l) < toInt(r) ? mkTrue() : mkFalse();
                }
                else if(l->isCReal() && r->isCReal()){
                    return toReal(l) < toReal(r) ? mkTrue() : mkFalse();
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_GE:{
                if(l->isCInt() && r->isCInt()){
                    return toInt(l) >= toInt(r) ? mkTrue() : mkFalse();
                }
                else if(l->isCReal() && r->isCReal()){
                    return toReal(l) >= toReal(r) ? mkTrue() : mkFalse();
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_GT:{
                if(l->isCInt() && r->isCInt()){
                    return toInt(l) > toInt(r) ? mkTrue() : mkFalse();
                }
                else if(l->isCReal() && r->isCReal()){
                    return toReal(l) > toReal(r) ? mkTrue() : mkFalse();
                }
                else{
                    return mkUnknown();
                }
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
                    return mkConstInt(gcd(toInt(l), toInt(r)));
                }
                else{
                    err_all(l, "GCD on non-integer", line_number);
                    err_all(r, "GCD on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_LCM:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(lcm(toInt(l), toInt(r)));
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
                    return mkConstBv(bvUdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_SDIV:{            
                // bvsdiv by zero evaluates to all ones if it's positive, otherwise 1.
                if(r->isCBV() && isZero(r)){
                    if(l->isCBV() && Integer(bvToInt(l->toString())) >= 0){
                        return mkConstBv("#b" + std::string(l->getSort()->getBitWidth(), '1'), l->getSort()->getBitWidth());
                    }
                    else{
                        return mkConstBv("#b" + std::string(l->getSort()->getBitWidth() - 1, '0') + "1", l->getSort()->getBitWidth());
                    }
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvSdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_UREM:{
                // remainder by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvUrem(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_SREM:{
                // bvsrem by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvSrem(l->toString(), r->toString()), r->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_UMOD:{
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvUmod(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_SMOD:{
                // bvsmod by zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvSmod(l->toString(), r->toString()), r->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
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
                    return mkConstBv(bvShl(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_LSHR:{
                // shift amount is zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvLshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_ASHR:{
                // shift amount is zero evaluates to the first operand.
                if(r->isCBV() && isZero(r)){
                    return l;
                }
                else if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvAshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    return mkUnknown();
                }
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
                    return bvComp(l->toString(), r->toString(), t) ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Comparison on non-bitvector", line_number);
                    err_all(r, "Comparison on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_NAT_TO_BV:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstBv(natToBv(toInt(l), toInt(r)), toInt(r).toULong());
                }
                else{
                    err_all(l, "Natural to bitvector on non-integer", line_number);
                    err_all(r, "Natural to bitvector on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_INT_TO_BV:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstBv(intToBv(toInt(l), toInt(r)), toInt(r).toULong());
                }
                else{
                    err_all(l, "Integer to bitvector on non-integer", line_number);
                    err_all(r, "Integer to bitvector on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_FP_DIV:
            case NODE_KIND::NT_FP_REM:
            case NODE_KIND::NT_FP_LE:
            case NODE_KIND::NT_FP_LT:
            case NODE_KIND::NT_FP_GE:
            case NODE_KIND::NT_FP_GT:
            case NODE_KIND::NT_FP_EQ:
            case NODE_KIND::NT_SELECT:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_PREFIXOF:{
                if(l->isCStr() && r->isCStr()){
                    return strPrefixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                else{   
                    err_all(l, "Prefixof on non-string", line_number);
                    err_all(r, "Prefixof on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_SUFFIXOF:{
                if(l->isCStr() && r->isCStr()){
                    return strSuffixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Suffixof on non-string", line_number);
                    err_all(r, "Suffixof on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_CHARAT:{
                if(l->isCStr() && r->isCInt()){
                    return mkConstStr(strCharAt(l->toString(), toInt(r)));
                }
                else{
                    err_all(l, "Charat on non-string", line_number);
                    err_all(r, "Charat on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_SPLIT:{
                return mkUnknown();
            }
            case NODE_KIND::NT_STR_LT:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() < r->toString() ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Lt on non-string", line_number);
                    err_all(r, "Lt on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_LE:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() <= r->toString() ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Le on non-string", line_number);
                    err_all(r, "Le on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_GT:{
                if(l->isCStr() && r->isCStr()){ 
                    return l->toString() > r->toString() ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Gt on non-string", line_number);
                    err_all(r, "Gt on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_GE:{
                if(l->isCStr() && r->isCStr()){
                    return l->toString() >= r->toString() ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Ge on non-string", line_number);
                    err_all(r, "Ge on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_CONTAINS:{
                if(l->isCStr() && r->isCStr()){
                    return strContains(l->toString(), r->toString()) ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Contains on non-string", line_number);
                    err_all(r, "Contains on non-string", line_number);
                    return mkUnknown();
                }
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
                if(l->toString() == r->toString()){
                    return mkFalse();
                }
                else{
                    return mkTrue();
                }
            }
            case NODE_KIND::NT_AND:{
                if(l->isFalse() || r->isFalse()){
                    return mkFalse();
                }
                else if(l->isTrue() || r->isTrue()){
                    return mkTrue();
                }
                else{
                    err_all(l, "And on non-boolean", line_number);
                    err_all(r, "And on non-boolean", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_OR:{
                if(l->isTrue() || r->isTrue()){
                    return mkTrue();
                }
                else if(l->isFalse() && r->isFalse()){
                    return mkFalse();
                }
                else{
                    err_all(l, "Or on non-boolean", line_number);
                    err_all(r, "Or on non-boolean", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_IMPLIES:{
                if(l->isTrue() && r->isFalse()){
                    return mkFalse();
                }
                else if(l->isFalse() || r->isTrue()){
                    return mkTrue();
                }
                else{
                    err_all(l, "Implies on non-boolean", line_number);
                    err_all(r, "Implies on non-boolean", line_number);
                    return mkUnknown();
                }
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
                else{
                    err_all(l, "Xor on non-boolean", line_number);
                    err_all(r, "Xor on non-boolean", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_ADD:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) + toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) + toReal(r));
                }
                else{
                    err_all(l, "Add on non-integer or non-real", line_number);
                    err_all(r, "Add on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_MUL:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) * toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) * toReal(r));
                }
                else{
                    err_all(l, "Mul on non-integer or non-real", line_number);
                    err_all(r, "Mul on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_IAND:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) & toInt(r));
                }
                else{
                    err_all(l, "Iand on non-integer", line_number);
                    err_all(r, "Iand on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_SUB:{
                if(l->isCInt() && r->isCInt()){
                    return mkConstInt(toInt(l) - toInt(r));
                }
                else if(l->isCReal() && r->isCReal()){
                    return mkConstReal(toReal(l) - toReal(r));
                }
                else{
                    err_all(l, "Sub on non-integer or non-real", line_number);
                    err_all(r, "Sub on non-integer or non-real", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_AND:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvAnd(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "And on non-bitvector", line_number);
                    err_all(r, "And on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_OR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvOr(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Or on non-bitvector", line_number);
                    err_all(r, "Or on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_XOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvXor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Xor on non-bitvector", line_number);
                    err_all(r, "Xor on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_NAND:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvNand(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Nand on non-bitvector", line_number);
                    err_all(r, "Nand on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_NOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvNor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Nor on non-bitvector", line_number);
                    err_all(r, "Nor on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_XNOR:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvXnor(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Xnor on non-bitvector", line_number);
                    err_all(r, "Xnor on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_COMP:{
                if(l->isCBV() && r->isCBV()){
                    return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_COMP) ? mkTrue() : mkFalse();
                }
                else{
                    err_all(l, "Comp on non-bitvector", line_number);
                    err_all(r, "Comp on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_ADD:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvAdd(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Add on non-bitvector", line_number);
                    err_all(r, "Add on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_SUB:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvSub(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Sub on non-bitvector", line_number);
                    err_all(r, "Sub on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_MUL:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvMul(l->toString(), r->toString()), l->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Mul on non-bitvector", line_number);
                    err_all(r, "Mul on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_BV_SADDO:
            case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SMULO:
            case NODE_KIND::NT_BV_UMULO:{
                return mkUnknown();
            }
            case NODE_KIND::NT_BV_CONCAT:{
                if(l->isCBV() && r->isCBV()){
                    return mkConstBv(bvConcat(l->toString(), r->toString()), l->getSort()->getBitWidth() + r->getSort()->getBitWidth());
                }
                else{
                    err_all(l, "Concat on non-bitvector", line_number);
                    err_all(r, "Concat on non-bitvector", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_CONCAT:{
                if(l->isCStr() && r->isCStr()){
                    return mkConstStr(l->toString() + r->toString());
                }
                else{
                    err_all(l, "Concat on non-string", line_number);
                    err_all(r, "Concat on non-string", line_number);
                    return mkUnknown();
                }
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
                    return mkConstStr(l->toString().substr(toInt(m).toULong(), toInt(r).toULong()));
                }
                else{
                    err_all(l, "Substr on non-string", line_number);
                    err_all(m, "Substr on non-integer", line_number);
                    err_all(r, "Substr on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_INDEXOF:{
                if(l->isCStr() && m->isCStr() && r->isCInt()){
                    return mkConstInt(l->toString().find(m->toString()));
                }
                else{
                    err_all(l, "Indexof on non-string", line_number);
                    err_all(m, "Indexof on non-string", line_number);
                    err_all(r, "Indexof on non-integer", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_UPDATE:{
                if(l->isCStr() && m->isCInt() && r->isCStr()){
                    return mkConstStr(strUpdate(l->toString(), toInt(m), r->toString()));
                }
                else{
                    err_all(l, "Update on non-string", line_number);
                    err_all(m, "Update on non-integer", line_number);
                    err_all(r, "Update on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_REPLACE:{
                if(l->isCStr() && m->isCStr() && r->isCStr()){
                    return mkConstStr(strReplace(l->toString(), m->toString(), r->toString()));
                }
                else{
                    err_all(l, "Replace on non-string", line_number);
                    err_all(m, "Replace on non-string", line_number);
                    err_all(r, "Replace on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_STR_REPLACE_ALL:{
                if(l->isCStr() && m->isCStr() && r->isCStr()){
                    return mkConstStr(strReplaceAll(l->toString(), m->toString(), r->toString()));
                }
                else{
                    err_all(l, "ReplaceAll on non-string", line_number);
                    err_all(m, "ReplaceAll on non-string", line_number);
                    err_all(r, "ReplaceAll on non-string", line_number);
                    return mkUnknown();
                }
            }
            case NODE_KIND::NT_REG_LOOP:
            case NODE_KIND::NT_REPLACE_REG:
            case NODE_KIND::NT_REPLACE_REG_ALL:
            case NODE_KIND::NT_INDEXOF_REG:{
                return mkUnknown();
            }
            // Special processing operation
            case NODE_KIND::NT_BV_EXTRACT:{
                if(l->isCBV() && m->isCInt() && r->isCInt()){
                    Integer size = (toInt(m) - toInt(r));
                    return mkConstBv(bvExtract(l->toString(), toInt(m), toInt(r)), size.toULong());
                }
                else{
                    err_all(l, "Extract on non-bitvector", line_number);
                    err_all(m, "Extract on non-integer", line_number);
                    err_all(r, "Extract on non-integer", line_number);
                    return mkUnknown();
                }
            }

            // Multi-parameter operation - accepts arbitrary number of parameters
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:{
                if(l->toString() == r->toString() && m->toString() == r->toString()){
                    return mkTrue();
                }
                else{
                    return mkFalse();
                }
            }
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:{
                if(l->toString() != m->toString() && l->toString() != r->toString() && m->toString() != r->toString()){
                    return mkTrue();
                }
                else{
                    return mkFalse();
                }
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
            case NODE_KIND::NT_STR_CONCAT:{
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
                auto common = p[0]->toString();
                for(size_t i=1;i<p.size();i++){
                    if(p[i]->toString() != common){
                        return mkFalse();
                    }
                }
                return mkTrue();
            }
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:{
                boost::unordered_set<std::string> s;
                for(size_t i=0;i<p.size();i++){
                    if(s.count(p[i]->toString())){
                        return mkFalse();
                    }
                    s.insert(p[i]->toString());
                }
                return mkTrue();
            }
            case NODE_KIND::NT_IMPLIES:{
                // -p[0] -p[1] -p[2] -p[3] ... p[n]
                for(size_t i=0;i<p.size();i++){
                    if(i != p.size()-1){
                        if(p[i]->isFalse()){
                            return mkTrue();
                        }
                    }
                    else{
                        if(p[i]->isTrue()){
                            return mkTrue();
                        }
                    }
                }
                return mkFalse();
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
            case NODE_KIND::NT_STR_CONCAT:{
                // convert to multi-pairs using {{l, m}, r}
                std::shared_ptr<DAGNode> result = p[0];
                for(size_t i=1;i<p.size();i++){
                    result = simp_oper(t, result, p[i]);
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
