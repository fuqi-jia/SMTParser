/* -*- Source -*-
 *
 * An SMT/OMT Parser (Evaluation part)
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

    void not_implemented_warning(const std::string& op){
        std::cerr << "Not implemented warning: " << op << " is not implemented" << std::endl;
    }

    std::shared_ptr<DAGNode> Parser::evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model){
        std::shared_ptr<DAGNode> result = NULL_NODE;
        evaluate(expr, model, result);
        return result;
    }
    bool Parser::evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model, std::shared_ptr<DAGNode> &result){
        if(model->isEmpty()){
            result = expr;
            return false;
        }
        if(expr->isUnknown()){
            return false;
        }
        else if(expr->isErr()){
            return false;
        }
        else if(expr->isConst()){
            result = expr;
            return false;
        }
        else if(expr->isVar()){
            result = model->get(expr);
            return result->isUnknown() ? false : true;
        }
        else if(expr->isAnd()){
            return evaluateAnd(expr, model, result);
        }
        else if(expr->isOr()){
            return evaluateOr(expr, model, result);
        }
        else if(expr->isNot()){
            return evaluateNot(expr, model, result);
        }
        else if(expr->isImpl()){
            return evaluateImpl(expr, model, result);
        }
        else if(expr->isXor()){
            return evaluateXor(expr, model, result);
        }
        else if(expr->isEq()){
            return evaluateEq(expr, model, result);
        }
        else if(expr->isDistinct()){
            return evaluateDistinct(expr, model, result);
        }
        else if(expr->isIte()){
            return evaluateIte(expr, model, result);
        }
        else if(expr->isAdd()){
            return evaluateAdd(expr, model, result);
        }
        else if(expr->isSub()){
            return evaluateSub(expr, model, result);
        }
        else if(expr->isMul()){
            return evaluateMul(expr, model, result);
        }
        else if(expr->isDivInt()){
            return evaluateDivInt(expr, model, result);
        }
        else if(expr->isDivReal()){
            return evaluateDivReal(expr, model, result);
        }
        else if(expr->isMod()){
            return evaluateMod(expr, model, result);
        }
        else if(expr->isPow()){
            return evaluatePow(expr, model, result);
        }
        else if(expr->isPow2()){
            return evaluatePow2(expr, model, result);
        }
        else if(expr->isIAnd()){
            return evaluateIand(expr, model, result);
        }
        else if(expr->isAbs()){
            return evaluateAbs(expr, model, result);
        }
        else if(expr->isSqrt()){
            return evaluateSqrt(expr, model, result);
        }
        else if(expr->isSafeSqrt()){
            return evaluateSafeSqrt(expr, model, result);
        }
        else if(expr->isCeil()){
            return evaluateCeil(expr, model, result);
        }
        else if(expr->isFloor()){
            return evaluateFloor(expr, model, result);
        }
        else if(expr->isRound()){
            return evaluateRound(expr, model, result);
        }
        else if(expr->isExp()){
            return evaluateExp(expr, model, result);
        }
        else if(expr->isLn()){
            return evaluateLn(expr, model, result);
        }
        else if(expr->isLg()){
            return evaluateLg(expr, model, result);
        }
        else if(expr->isLn()){
            return evaluateLn(expr, model, result);
        }
        else if(expr->isLog()){
            return evaluateLog(expr, model, result);
        }
        else if(expr->isLb()){
            return evaluateLb(expr, model, result);
        }
        else if(expr->isSin()){
            return evaluateSin(expr, model, result);
        }
        else if(expr->isCos()){
            return evaluateCos(expr, model, result);
        }
        else if(expr->isTan()){
            return evaluateTan(expr, model, result);
        }
        else if(expr->isAsin()){
            return evaluateAsin(expr, model, result);
        }
        else if(expr->isAcos()){
            return evaluateAcos(expr, model, result);
        }
        else if(expr->isAtan()){
            return evaluateAtan(expr, model, result);
        }
        else if(expr->isSinh()){
            return evaluateSinh(expr, model, result);
        }
        else if(expr->isCosh()){
            return evaluateCosh(expr, model, result);
        }
        else if(expr->isTanh()){
            return evaluateTanh(expr, model, result);
        }
        else if(expr->isAsinh()){
            return evaluateAsinh(expr, model, result);
        }
        else if(expr->isAcosh()){
            return evaluateAcosh(expr, model, result);
        }
        else if(expr->isAtanh()){
            return evaluateAtanh(expr, model, result);
        }
        else if(expr->isAsech()){
            return evaluateAsech(expr, model, result);
        }
        else if(expr->isAcsch()){
            return evaluateAcsch(expr, model, result);
        }
        else if(expr->isAcoth()){
            return evaluateAcoth(expr, model, result);
        }
        else if(expr->isAtan2()){
            return evaluateAtan2(expr, model, result);
        }
        else if(expr->isLe()){
            return evaluateLe(expr, model, result);
        }
        else if(expr->isLt()){
            return evaluateLt(expr, model, result);
        }
        else if(expr->isGe()){
            return evaluateGe(expr, model, result);
        }
        else if(expr->isGt()){
            return evaluateGt(expr, model, result);
        }
        else if(expr->isToReal()){
            return evaluateToReal(expr, model, result);
        }
        else if(expr->isToInt()){
            return evaluateToInt(expr, model, result);
        }
        else if(expr->isInt()){
            return evaluateIsInt(expr, model, result);
        }
        else if(expr->isDivisible()){
            return evaluateIsDivisible(expr, model, result);
        }
        else if(expr->isPrime()){
            return evaluateIsPrime(expr, model, result);
        }
        else if(expr->isEven()){
            return evaluateIsEven(expr, model, result);
        }
        else if(expr->isOdd()){
            return evaluateIsOdd(expr, model, result);
        }
        else if(expr->isGcd()){
            return evaluateGcd(expr, model, result);
        }
        else if(expr->isLcm()){
            return evaluateLcm(expr, model, result);
        }
        else if(expr->isFact()){
            return evaluateFact(expr, model, result);
        }
        else if(expr->isBVNot()){
            return evaluateBvNot(expr, model, result);
        }
        else if(expr->isBVNeg()){
            return evaluateBvNeg(expr, model, result);
        }
        else if(expr->isBVAnd()){
            return evaluateBvAnd(expr, model, result);
        }
        else if(expr->isBVOr()){
            return evaluateBvOr(expr, model, result);
        }
        else if(expr->isBVXor()){
            return evaluateBvXor(expr, model, result);
        }
        else if(expr->isBVNand()){
            return evaluateBvNand(expr, model, result);
        }
        else if(expr->isBVNor()){
            return evaluateBvNor(expr, model, result);
        }
        else if(expr->isBVXnor()){
            return evaluateBvXnor(expr, model, result);
        }
        else if(expr->isBVComp()){
            return evaluateBvComp(expr, model, result);
        }
        else if(expr->isBVAdd()){
            return evaluateBvAdd(expr, model, result);
        }
        else if(expr->isBVSub()){
            return evaluateBvSub(expr, model, result);
        }
        else if(expr->isBVMul()){
            return evaluateBvMul(expr, model, result);
        }
        else if(expr->isBVUDiv()){
            return evaluateBvUdiv(expr, model, result);
        }
        else if(expr->isBVURem()){
            return evaluateBvUrem(expr, model, result);
        }
        else if(expr->isBVSDiv()){
            return evaluateBvSdiv(expr, model, result);
        }
        else if(expr->isBVSRem()){
            return evaluateBvSrem(expr, model, result);
        }
        else if(expr->isBVSMod()){
            return evaluateBvSmod(expr, model, result);
        }
        else if(expr->isBVShl()){
            return evaluateBvShl(expr, model, result);
        }
        else if(expr->isBVLSHR()){
            return evaluateBvLshr(expr, model, result);
        }
        else if(expr->isBVASHR()){
            return evaluateBvAshr(expr, model, result);
        }
        else if(expr->isBVUlt()){
            return evaluateBvUlt(expr, model, result);
        }
        else if(expr->isBVUle()){
            return evaluateBvUle(expr, model, result);
        }
        else if(expr->isBVUgt()){
            return evaluateBvUgt(expr, model, result);
        }
        else if(expr->isBVUge()){
            return evaluateBvUge(expr, model, result);
        }
        else if(expr->isBVSlt()){
            return evaluateBvSlt(expr, model, result);
        }
        else if(expr->isBVSle()){
            return evaluateBvSle(expr, model, result);
        }
        else if(expr->isBVSgt()){
            return evaluateBvSgt(expr, model, result);
        }
        else if(expr->isBVSge()){
            return evaluateBvSge(expr, model, result);
        }
        else if(expr->isBVConcat()){
            return evaluateBvConcat(expr, model, result);
        }
        else if(expr->isBVToNat()){
            return evaluateBvToNat(expr, model, result);
        }
        else if(expr->isNatToBV()){
            return evaluateBvNatToBv(expr, model, result);
        }
        else if(expr->isIntToBV()){
            return evaluateBvIntToBv(expr, model, result);
        }
        else if(expr->isBVToInt()){
            return evaluateBvToInt(expr, model, result);
        }
        else if(expr->isFPAbs()){
            return evaluateFpAbs(expr, model, result);
        }
        else if(expr->isFPNeg()){
            return evaluateFpNeg(expr, model, result);
        }
        else if(expr->isFPAdd()){
            return evaluateFpAdd(expr, model, result);
        }
        else if(expr->isFPSub()){
            return evaluateFpSub(expr, model, result);
        }
        else if(expr->isFPMul()){
            return evaluateFpMul(expr, model, result);
        }
        else if(expr->isFPDiv()){
            return evaluateFpDiv(expr, model, result);
        }
        else if(expr->isFPFMA()){
            return evaluateFpFma(expr, model, result);
        }
        else if(expr->isFPSqrt()){
            return evaluateFpSqrt(expr, model, result);
        }
        else if(expr->isFPRem()){
            return evaluateFpRem(expr, model, result);
        }
        else if(expr->isFPRoundToIntegral()){
            return evaluateFpRoundToIntegral(expr, model, result);
        }
        else if(expr->isFPMin()){
            return evaluateFpMin(expr, model, result);
        }
        else if(expr->isFPMax()){
            return evaluateFpMax(expr, model, result);
        }
        else if(expr->isFPLe()){
            return evaluateFpLe(expr, model, result);
        }
        else if(expr->isFPLt()){
            return evaluateFpLt(expr, model, result);
        }
        else if(expr->isFPGe()){
            return evaluateFpGe(expr, model, result);
        }
        else if(expr->isFPGt()){
            return evaluateFpGt(expr, model, result);
        }
        else if(expr->isFPEq()){
            return evaluateFpEq(expr, model, result);
        }
        else if(expr->isFPToUBV()){
            return evaluateFpToUbv(expr, model, result);
        }
        else if(expr->isFPToSBV()){
            return evaluateFpToSbv(expr, model, result);
        }
        else if(expr->isFPToReal()){
            return evaluateFpToReal(expr, model, result);
        }
        else if(expr->isToFP()){
            return evaluateToFp(expr, model, result);
        }
        else if(expr->isFPIsNormal()){
            return evaluateFpIsNormal(expr, model, result);
        }
        else if(expr->isFPIsSubnormal()){
            return evaluateFpIsSubnormal(expr, model, result);
        }
        else if(expr->isFPIsZero()){
            return evaluateFpIsZero(expr, model, result);
        }
        else if(expr->isFPIsInf()){
            return evaluateFpIsInf(expr, model, result);
        }
        else if(expr->isFPIsNan()){
            return evaluateFpIsNan(expr, model, result);
        }
        else if(expr->isFPIsNeg()){
            return evaluateFpIsNeg(expr, model, result);
        }
        else if(expr->isFPIsPos()){
            return evaluateFpIsPos(expr, model, result);
        }
        else if(expr->isSelect()){
            return evaluateSelect(expr, model, result);
        }
        else if(expr->isStore()){
            return evaluateStore(expr, model, result);
        }
        else if(expr->isStrLen()){
            return evaluateStrLen(expr, model, result);
        }
        else if(expr->isStrConcat()){
            return evaluateStrConcat(expr, model, result);
        }
        else if(expr->isStrSubstr()){
            return evaluateStrSubstr(expr, model, result);
        }
        else if(expr->isStrPrefixof()){
            return evaluateStrPrefixof(expr, model, result);
        }
        else if(expr->isStrSuffixof()){
            return evaluateStrSuffixof(expr, model, result);
        }
        else if(expr->isStrIndexof()){
            return evaluateStrIndexof(expr, model, result);
        }
        else if(expr->isStrCharat()){
            return evaluateStrCharat(expr, model, result);
        }
        else if(expr->isStrUpdate()){
            return evaluateStrUpdate(expr, model, result);
        }
        else if(expr->isStrReplace()){
            return evaluateStrReplace(expr, model, result);
        }
        else if(expr->isStrReplaceAll()){
            return evaluateStrReplaceAll(expr, model, result);
        }
        else if(expr->isStrToLower()){
            return evaluateStrToLower(expr, model, result);
        }
        else if(expr->isStrToUpper()){
            return evaluateStrToUpper(expr, model, result);
        }
        else if(expr->isStrRev()){
            return evaluateStrRev(expr, model, result);
        }
        else if(expr->isStrSplit()){
            return evaluateStrSplit(expr, model, result);
        }
        else if(expr->isStrLt()){
            return evaluateStrLt(expr, model, result);
        }
        else if(expr->isStrLe()){
            return evaluateStrLe(expr, model, result);
        }
        else if(expr->isStrGt()){
            return evaluateStrGt(expr, model, result);
        }
        else if(expr->isStrGe()){
            return evaluateStrGe(expr, model, result);
        }
        else if(expr->isStrInReg()){
            return evaluateStrInReg(expr, model, result);
        }
        else if(expr->isStrContains()){
            return evaluateStrContains(expr, model, result);
        }
        else if(expr->isStrIsDigit()){
            return evaluateStrIsDigit(expr, model, result);
        }
        else if(expr->isStrFromInt()){
            return evaluateStrFromInt(expr, model, result);
        }
        else if(expr->isStrToInt()){
            return evaluateStrToInt(expr, model, result);
        }
        else if(expr->isStrToReg()){
            return evaluateStrToReg(expr, model, result);
        }
        else if(expr->isStrToCode()){
            return evaluateStrToCode(expr, model, result);
        }
        else if(expr->isStrFromCode()){
            return evaluateStrFromCode(expr, model, result);
        }
        else if(expr->isRegConcat()){
            return evaluateRegConcat(expr, model, result);
        }
        else if(expr->isRegUnion()){
            return evaluateRegUnion(expr, model, result);
        }
        else if(expr->isRegInter()){
            return evaluateRegInter(expr, model, result);
        }
        else if(expr->isRegDiff()){
            return evaluateRegDiff(expr, model, result);
        }
        else if(expr->isRegStar()){
            return evaluateRegStar(expr, model, result);
        }
        else if(expr->isRegPlus()){
            return evaluateRegPlus(expr, model, result);
        }
        else if(expr->isRegOpt()){
            return evaluateRegOpt(expr, model, result);
        }
        else if(expr->isRegRange()){
            return evaluateRegRange(expr, model, result);
        }
        else if(expr->isRegRepeat()){
            return evaluateRegRepeat(expr, model, result);
        }
        else if(expr->isRegComplement()){
            return evaluateRegComplement(expr, model, result);
        }
        else if(expr->isFuncApply()){
            return evaluateApplyFun(expr, model, result);
        }
        result = expr;
        return false;
    }

    bool Parser::evaluateSimpleOp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result, NODE_KIND op){
        bool changed = false;
        switch(op){
            // unary operations
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_ABS:
            case NODE_KIND::NT_SQRT:
            case NODE_KIND::NT_SAFESQRT:
            case NODE_KIND::NT_CEIL:
            case NODE_KIND::NT_FLOOR:
            case NODE_KIND::NT_ROUND:
            case NODE_KIND::NT_EXP:
            case NODE_KIND::NT_LN:
            case NODE_KIND::NT_LG:
            case NODE_KIND::NT_LB:
            case NODE_KIND::NT_SIN:
            case NODE_KIND::NT_COS:
            case NODE_KIND::NT_TAN:
            case NODE_KIND::NT_ASIN:
            case NODE_KIND::NT_ACOS:
            case NODE_KIND::NT_ATAN:
            case NODE_KIND::NT_SINH:
            case NODE_KIND::NT_COSH:
            case NODE_KIND::NT_TANH:
            case NODE_KIND::NT_ASINH:
            case NODE_KIND::NT_ACOSH:
            case NODE_KIND::NT_ATANH:
            case NODE_KIND::NT_ASEC:
            case NODE_KIND::NT_ACSC:
            case NODE_KIND::NT_ACOT:
            case NODE_KIND::NT_SECH:
            case NODE_KIND::NT_CSCH:
            case NODE_KIND::NT_COTH:
            case NODE_KIND::NT_TO_REAL:
            case NODE_KIND::NT_TO_INT:
            case NODE_KIND::NT_IS_INT:
            case NODE_KIND::NT_IS_DIVISIBLE:
            case NODE_KIND::NT_IS_PRIME:
            case NODE_KIND::NT_IS_EVEN:
            case NODE_KIND::NT_IS_ODD:
            case NODE_KIND::NT_FACT:
            case NODE_KIND::NT_BV_NOT:
            case NODE_KIND::NT_BV_NEG:
            case NODE_KIND::NT_BV_TO_NAT:
            case NODE_KIND::NT_BV_TO_INT:
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
            {
                std::shared_ptr<DAGNode> child = NULL_NODE;
                changed |= evaluate(expr->getChildren()[0], model, child);
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                result = mkOper(expr->getSort(), op, child);
                return true;
            }
            // binary operations
            case NODE_KIND::NT_IMPLIES:
            case NODE_KIND::NT_LOG:
            case NODE_KIND::NT_ATAN2:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_GCD:
            case NODE_KIND::NT_LCM:
            case NODE_KIND::NT_BV_COMP:
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
            case NODE_KIND::NT_BV_SGT:
            case NODE_KIND::NT_BV_SLE:
            case NODE_KIND::NT_BV_SGE:
            case NODE_KIND::NT_NAT_TO_BV:
            case NODE_KIND::NT_INT_TO_BV:
            case NODE_KIND::NT_STR_PREFIXOF:
            case NODE_KIND::NT_STR_SUFFIXOF:
            case NODE_KIND::NT_STR_CONTAINS:
            case NODE_KIND::NT_STR_CHARAT:
            case NODE_KIND::NT_STR_LT:
            case NODE_KIND::NT_STR_LE:
            case NODE_KIND::NT_STR_GT:
            case NODE_KIND::NT_STR_GE:
            case NODE_KIND::NT_STR_IN_REG:
            {
                std::shared_ptr<DAGNode> l = NULL_NODE;
                std::shared_ptr<DAGNode> r = NULL_NODE;
                changed |= evaluate(expr->getChildren()[0], model, l);
                changed |= evaluate(expr->getChildren()[1], model, r);
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                result = mkOper(expr->getSort(), op, l, r);
                return true;
            }
            // triple operations
            case NODE_KIND::NT_STR_SUBSTR:
            case NODE_KIND::NT_STR_INDEXOF:
            case NODE_KIND::NT_STR_UPDATE:
            case NODE_KIND::NT_STR_REPLACE:
            case NODE_KIND::NT_STR_REPLACE_ALL:
            {
                bool changed = false;
                std::shared_ptr<DAGNode> l = NULL_NODE;
                std::shared_ptr<DAGNode> r = NULL_NODE;
                std::shared_ptr<DAGNode> s = NULL_NODE;
                changed |= evaluate(expr->getChildren()[0], model, l);
                changed |= evaluate(expr->getChildren()[1], model, r);
                changed |= evaluate(expr->getChildren()[2], model, s);
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                result = mkOper(expr->getSort(), op, {l, r, s});
                return true;
            }
            // simplify using binary operations
            case NODE_KIND::NT_IAND:
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_BV_AND:
            case NODE_KIND::NT_BV_OR:
            case NODE_KIND::NT_BV_XOR:
            case NODE_KIND::NT_BV_NAND:
            case NODE_KIND::NT_BV_NOR:
            case NODE_KIND::NT_BV_XNOR:
            case NODE_KIND::NT_BV_ADD:
            case NODE_KIND::NT_BV_MUL:
            {
                changed = false;
                std::vector<std::shared_ptr<DAGNode>> children;
                for(auto child : expr->getChildren()){
                    std::shared_ptr<DAGNode> eval = NULL_NODE;
                    changed |= evaluate(child, model, eval);
                    children.emplace_back(eval);
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                assert(!children.empty());
                // compute the sum of the children that are constant
                std::vector<std::shared_ptr<DAGNode>> const_children;
                std::vector<std::shared_ptr<DAGNode>> non_const_children;
                for(auto child : children){
                    if(child->isConst()){
                        const_children.emplace_back(child);
                    }
                    else{
                        non_const_children.emplace_back(child);
                    }
                }
                if(const_children.empty()){
                    result = mkOper(expr->getSort(), op, non_const_children);
                }
                else{
                    // compute the and of the constant children
                    result = const_children[0];
                    for(size_t i = 1; i < const_children.size(); ++i){
                        result = mkOper(expr->getSort(), op, result, const_children[i]);
                    }
                    non_const_children.emplace_back(result);
                    if(non_const_children.size() == 1){
                        result = non_const_children[0];
                    }
                    else{
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                }
                return true; 
            }
            // simplify using binary operations but the first child is special
            case NODE_KIND::NT_SUB:
            case NODE_KIND::NT_DIV_REAL:
            case NODE_KIND::NT_BV_SUB:
            case NODE_KIND::NT_BV_UDIV:
            case NODE_KIND::NT_BV_SDIV:
            case NODE_KIND::NT_FP_SUB:
            {
                changed = false;
                std::vector<std::shared_ptr<DAGNode>> children;
                for(auto child : expr->getChildren()){
                    std::shared_ptr<DAGNode> eval = NULL_NODE;
                    changed |= evaluate(child, model, eval);
                    children.emplace_back(eval);
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                assert(!children.empty());
                // compute the difference of the children that are constant
                bool first_child_is_const = children[0]->isConst();
                std::vector<std::shared_ptr<DAGNode>> const_children;
                std::vector<std::shared_ptr<DAGNode>> non_const_children;
                for(auto child : children){
                    if(child->isConst()){
                        const_children.emplace_back(child);
                    }
                    else{
                        non_const_children.emplace_back(child);
                    }
                }
                if(const_children.empty()){
                    result = mkSub(non_const_children);
                }
                else{
                    if(first_child_is_const){
                        result = const_children[0];
                        for(size_t i = 1; i < const_children.size(); ++i){
                            result = mkOper(expr->getSort(), op, result, const_children[i]);
                        }
                        non_const_children.insert(non_const_children.begin(), result);
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                    else{
                        auto opposite_op = getOppositeKind(op);
                        for(auto child : const_children){
                            result = mkOper(expr->getSort(), opposite_op, result, child);
                        }
                        non_const_children.emplace_back(result);
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                }
                return true;
            }
            // concat
            case NODE_KIND::NT_BV_CONCAT:
            case NODE_KIND::NT_STR_CONCAT:
            {
                changed = false;
                // sequential evaluation
                std::vector<std::shared_ptr<DAGNode>> children;
                size_t i = 0;
                while(i < expr->getChildren().size()){
                    // concat until the last constant child
                    std::shared_ptr<DAGNode> child = NULL_NODE;
                    changed |= evaluate(expr->getChildren()[i], model, child);
                    if(child->isConst()){
                        // go on until the child is not constant
                        std::shared_ptr<DAGNode> child_ = NULL_NODE;
                        while(i < expr->getChildren().size()){
                            changed |= evaluate(expr->getChildren()[i], model, child_);
                            if(!child_->isConst()) break;
                            child = mkOper(expr->getSort(), op, child, child_);
                            i++;
                        }
                        if(i == expr->getChildren().size()){
                            // all remaining children are constant
                            children.push_back(child);
                            break;
                        }
                        else if(child_->isNull()){
                            // child_ is null -> only child is constant
                            children.push_back(child);
                        }
                        else{
                            assert(!child->isConst());
                            children.push_back(child);
                        }
                    }
                    else{
                        children.emplace_back(child);
                    }
                    i++;
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                assert(changed);
                assert(!children.empty());
                if(children.size() == 1){
                    result = children.back();
                    return false;
                }
                else{
                    result = mkOper(expr->getSort(), op, children);
                }
                return true;
            }
            default:
                assert(false);
                result = expr;
                return false;
        }

        return changed;
    }
    bool Parser::evaluateAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        std::vector<std::shared_ptr<DAGNode>> children;
        bool changed = false;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NULL_NODE;
            changed |= evaluate(child, model, eval);
            if(eval->isConst()){
                if(eval->isFalse()){
                    result = eval;
                    return true; // result has been changed
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(children.empty()){
            result = mkTrue();
        }
        else if(children.size() == 1){
            result = children[0];
        }
        else{
            result = mkAnd(children);
        }
        return true;
    }
    bool Parser::evaluateOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        std::vector<std::shared_ptr<DAGNode>> children;
        bool changed = false;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NULL_NODE;
            changed |= evaluate(child, model, eval);
            if(eval->isConst()){
                if(eval->isTrue()){
                    result = eval;
                    return true;
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(children.empty()){
            result = mkFalse();
        }
        else if(children.size() == 1){
            result = children[0];
        }
        else{
            result = mkOr(children);
        }
        return true;
    }
    bool Parser::evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NOT);
    }
    bool Parser::evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IMPLIES);
    }
    bool Parser::evaluateXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        // count true
        size_t trueCount = 0;
        // save unevaluated children
        std::vector<std::shared_ptr<DAGNode>> remainingChildren;
        
        // traverse all children
        for (auto child : expr->getChildren()) {
            std::shared_ptr<DAGNode> evaluatedChild = NULL_NODE;
            changed |= evaluate(child, model, evaluatedChild);
            
            // evaluated as constant
            if (evaluatedChild->isConst()) {
                if (evaluatedChild->isTrue()) {
                    trueCount++;
                }
                // ignore false
            } else {
                // save unevaluated children
                remainingChildren.emplace_back(evaluatedChild);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        // all children are constants
        if (remainingChildren.empty()) {
            // result depends on true count is odd or even
            result = (trueCount % 2 == 1) ? mkTrue() : mkFalse();
            return true;
        }
        
        // only one unevaluated child
        if (remainingChildren.size() == 1) {
            // if true count is even, result is the child
            // if true count is odd, result is the negation of the child
            result = (trueCount % 2 == 0) ? 
                   remainingChildren[0] : 
                   mkNot(remainingChildren[0]);
            return true;
        }
        
        // multiple unevaluated children
        // decide return XOR or its negation based on true count
        result = (trueCount % 2 == 0) ? 
                   mkXor(remainingChildren) : 
                   mkNot(mkXor(remainingChildren));
        return true;
    }
    bool Parser::evaluateEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        std::shared_ptr<DAGNode> const_val = NULL_NODE;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NULL_NODE;
            changed |= evaluate(child, model, eval);
            if(eval->isConst()){
                if(const_val->toString() != eval->toString()){
                    result = mkFalse();
                    return true;
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(children.empty()){
            result = const_val->isTrue() ? mkTrue() : mkFalse();
        }
        else if(children.size() == 1){
            assert(!const_val->isNull());
            result = mkEq(children[0], const_val);
        }
        else{
            if(const_val->isNull()){
                result = mkEq(children);
            }
            else{
                children.emplace_back(const_val);
                result = mkEq(children);
            }
        }
        return true;
    }
    bool Parser::evaluateDistinct(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        boost::unordered_set<std::shared_ptr<DAGNode>> const_vals;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NULL_NODE;
            changed |= evaluate(child, model, eval);
            if(eval->isConst()){
                if(const_vals.empty()){
                    const_vals.insert(eval);
                }
                else if(const_vals.find(eval) == const_vals.end()){
                    const_vals.insert(eval);
                }
                else{
                    result = mkFalse();
                    return true;
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(children.empty()){
            assert(const_vals.size() == expr->getChildrenSize());
            result = mkTrue();
        }
        else{
            children.insert(children.end(), const_vals.begin(), const_vals.end());
            result = mkDistinct(children);
        }
        return true;
    }
    bool Parser::evaluateIte(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::shared_ptr<DAGNode> cond = NULL_NODE;
        std::shared_ptr<DAGNode> then_child = NULL_NODE;
        std::shared_ptr<DAGNode> else_child = NULL_NODE;
        changed |= evaluate(expr->getChild(0), model, cond);
        changed |= evaluate(expr->getChild(1), model, then_child);
        changed |= evaluate(expr->getChild(2), model, else_child);
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(cond->isConst()){
            result = cond->isTrue() ? then_child : else_child;
        }
        else{
            result = mkIte(cond, then_child, else_child);
        }
        return true;
    }
    bool Parser::evaluateAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ADD);
    }
    bool Parser::evaluateSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SUB);
	}
    bool Parser::evaluateMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MUL);
	}
    bool Parser::evaluateDivInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NULL_NODE;
            changed |= evaluate(child, model, eval);
            children.emplace_back(eval);
        }
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        assert(!children.empty());
        // compute the quotient of the children that are constant
        bool first_child_is_const = children[0]->isConst();
        std::vector<std::shared_ptr<DAGNode>> const_children;
        std::vector<std::shared_ptr<DAGNode>> non_const_children;
        for(auto child : children){
            if(child->isConst()){
                const_children.emplace_back(child);
            }
            else{
                non_const_children.emplace_back(child);
            }
        }
        if(const_children.empty()){
            result = mkDivInt(non_const_children);
        }
        else{
            if(first_child_is_const){
                auto res = mkConstInt(1);
                for(size_t i = 1; i < const_children.size(); ++i){
                    res = mkMul({res, const_children[i]});
                }
                if(res->toInt() > const_children[0]->toInt()){
                    // 1 / 3 is 0 in integer arithmetic
                    result = mkConstInt(0);
                    return true;
                }
                else{
                    // 5 / 3 is 1 in integer arithmetic
                    auto div = mkDivInt({const_children[0], res});
                    non_const_children.insert(non_const_children.begin(), div);
                }
            }
            else{
                auto res = mkConstInt(1);
                for(size_t i = 0; i < const_children.size(); ++i){
                    res = mkMul({res, const_children[i]});
                }
                non_const_children.emplace_back(res);
                result = mkDivInt(non_const_children);
            }
        }
        return true;
	}
    bool Parser::evaluateDivReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_DIV_REAL);
	}   
    bool Parser::evaluateMod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MOD);
	}
    bool Parser::evaluatePow(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_POW);
    }
    bool Parser::evaluatePow2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_POW2);
	}
    bool Parser::evaluateIand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IAND);
    }
    bool Parser::evaluateAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ABS);
	}
    bool Parser::evaluateSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SQRT);
	}
    bool Parser::evaluateSafeSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SAFESQRT);
	}
    bool Parser::evaluateCeil(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_CEIL);
	}
    bool Parser::evaluateFloor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_FLOOR);
	}
    bool Parser::evaluateRound(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ROUND);
	}
    bool Parser::evaluateExp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_EXP);
	}
    bool Parser::evaluateLn(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LN);
	}
    bool Parser::evaluateLg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LG);
	}
    bool Parser::evaluateLog(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LOG);
	}
    bool Parser::evaluateLb(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LB);
	}
    bool Parser::evaluateSin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SIN);
	}
    bool Parser::evaluateCos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COS);
	}
    bool Parser::evaluateTan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TAN);
	}
    bool Parser::evaluateAsin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASIN);
	}
    bool Parser::evaluateAcos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOS);
	}
    bool Parser::evaluateAtan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATAN);
	}
    bool Parser::evaluateSinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SINH);
	}
    bool Parser::evaluateCosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COSH);
	}
    bool Parser::evaluateTanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TANH);
	}
    bool Parser::evaluateAsinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASINH);
	}
    bool Parser::evaluateAcosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOSH);
	}
    bool Parser::evaluateAtanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATANH);
	}
    bool Parser::evaluateAsech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASECH);
	}
    bool Parser::evaluateAcsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACSCH);
	}
    bool Parser::evaluateAcoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOTH);
	}
    bool Parser::evaluateAtan2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATAN2);
	}
    bool Parser::evaluateLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LE);
	}
    bool Parser::evaluateLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LT);
	}
    bool Parser::evaluateGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GE);
	}
    bool Parser::evaluateGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GT);
	}
    bool Parser::evaluateToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TO_REAL);
	}
    bool Parser::evaluateToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TO_INT);
	}
    bool Parser::evaluateIsInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_INT);
	}
    bool Parser::evaluateIsDivisible(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_DIVISIBLE);
	}
    bool Parser::evaluateIsPrime(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_PRIME);
	}
    bool Parser::evaluateIsEven(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_EVEN);
	}
    bool Parser::evaluateIsOdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_ODD);
	}
    bool Parser::evaluateGcd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GCD);
	}
    bool Parser::evaluateLcm(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LCM);
	}
    bool Parser::evaluateFact(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_FACT);
	}
    bool Parser::evaluateBvNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NOT);
	}
    bool Parser::evaluateBvNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NEG);
	}
    bool Parser::evaluateBvAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_AND);
	}
    bool Parser::evaluateBvOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_OR);
	}
    bool Parser::evaluateBvXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_XOR);
	}
    bool Parser::evaluateBvNand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NAND);
	}
    bool Parser::evaluateBvNor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NOR);
	}
    bool Parser::evaluateBvXnor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_XNOR);
	}
    bool Parser::evaluateBvComp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_COMP);
	}
    bool Parser::evaluateBvAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ADD);
	}
    bool Parser::evaluateBvSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SUB);
	}
    bool Parser::evaluateBvMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_MUL);
	}
    bool Parser::evaluateBvUdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UDIV);
	}
    bool Parser::evaluateBvUrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UREM);
	}
    bool Parser::evaluateBvSdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SDIV);
	}
    bool Parser::evaluateBvSrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SREM);
	}
    bool Parser::evaluateBvSmod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SMOD);
	}
    bool Parser::evaluateBvShl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SHL);
	}
    bool Parser::evaluateBvLshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_LSHR);
	}
    bool Parser::evaluateBvAshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ASHR);
	}
    bool Parser::evaluateBvUlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ULT);
	}
    bool Parser::evaluateBvUle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ULE);
	}
    bool Parser::evaluateBvUgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UGT);
	}
    bool Parser::evaluateBvUge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UGE);
	}
    bool Parser::evaluateBvSlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SLT);
	}
    bool Parser::evaluateBvSle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SLE);
	}
    bool Parser::evaluateBvSgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SGT);
	}
    bool Parser::evaluateBvSge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SGE);
	}
    bool Parser::evaluateBvConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_CONCAT);
    }
    bool Parser::evaluateBvToNat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_TO_NAT);
	}
    bool Parser::evaluateBvNatToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NAT_TO_BV);
	}
    bool Parser::evaluateBvIntToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_TO_INT);
	}
    bool Parser::evaluateBvToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NAT_TO_BV);
	}
    bool Parser::evaluateFpAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.abs");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.neg");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.add");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.sub");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.mul");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpDiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.div");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpFma(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.fma");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.sqrt");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpRem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.rem");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpRoundToIntegral(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.roundToIntegral");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.min");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.max");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.le");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.lt");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.ge");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.gt");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.eq");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpToUbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.toUbv");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpToSbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.toSbv");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.toReal");
        result = expr;
        return false;
	}   
    bool Parser::evaluateToFp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.toFp");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsNormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isNormal");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsSubnormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isSubnormal");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsZero(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isZero");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsInf(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isInf");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsNan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isNan");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isNeg");
        result = expr;
        return false;
	}
    bool Parser::evaluateFpIsPos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("fp.isPos");
        result = expr;
        return false;
	}
    bool Parser::evaluateSelect(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("select");
        result = expr;
        return false;
	}
    bool Parser::evaluateStore(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("store");
        result = expr;
        return false;
	}
    bool Parser::evaluateStrLen(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LEN);
    }
    bool Parser::evaluateStrConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CONCAT);
    }
    bool Parser::evaluateStrSubstr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SUBSTR);
	}
    bool Parser::evaluateStrPrefixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_PREFIXOF);
	}
    bool Parser::evaluateStrSuffixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SUFFIXOF);
	}
    bool Parser::evaluateStrIndexof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_INDEXOF);
	}
    bool Parser::evaluateStrCharat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CHARAT);
	}
    bool Parser::evaluateStrUpdate(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_UPDATE);
	}
    bool Parser::evaluateStrReplace(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REPLACE);
	}
    bool Parser::evaluateStrReplaceAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REPLACE_ALL);
	}
    bool Parser::evaluateStrToLower(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_LOWER);
	}
    bool Parser::evaluateStrToUpper(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_UPPER);
	}
    bool Parser::evaluateStrRev(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REV);
	}
    bool Parser::evaluateStrSplit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("str.split");
        result = expr;
        return false;
	}
    bool Parser::evaluateStrLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LT);
	}   
    bool Parser::evaluateStrLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LE);
	}
    bool Parser::evaluateStrGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_GT);
	}
    bool Parser::evaluateStrGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_GE);
	}
    bool Parser::evaluateStrInReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_IN_REG);
	}
    bool Parser::evaluateStrContains(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CONTAINS);
	}
    bool Parser::evaluateStrIsDigit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_IS_DIGIT);
	}
    bool Parser::evaluateStrFromInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_FROM_INT);
	}
    bool Parser::evaluateStrToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_INT);
	}
    bool Parser::evaluateStrToReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_REG);
	}
    bool Parser::evaluateStrToCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_CODE);
	}
    bool Parser::evaluateStrFromCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_FROM_CODE);
	}
    bool Parser::evaluateRegConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.concat");
        result = expr;
        return false;
    }
    bool Parser::evaluateRegUnion(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.union");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegInter(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.inter");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegDiff(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.diff");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegStar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.star");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegPlus(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.plus");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegOpt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.opt");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegRange(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.range");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.repeat");
        result = expr;
        return false;
	}
    bool Parser::evaluateRegComplement(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
		not_implemented_warning("reg.complement");
        result = expr;
        return false;
	}
    bool Parser::evaluateApplyFun(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        (void)model;
		not_implemented_warning("function-apply");
        result = expr;
        return false;
    }
}


