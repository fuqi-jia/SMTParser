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
std::shared_ptr<DAGNode> Parser::parseOper(const std::string& s, const std::vector<std::shared_ptr<DAGNode>> &params){;

    void precision_warning(const std::string& op){
        std::cerr << "Precision warning: " << op << " will use double precision" << std::endl;
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
        else if(expr->isError()){
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
        else if(expr->isIand()){
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
        else if(expr->isIsInt()){
            return evaluateIsInt(expr, model, result);
        }
        else if(expr->isIsDivisible()){
            return evaluateIsDivisible(expr, model, result);
        }
        else if(expr->isIsPrime()){
            return evaluateIsPrime(expr, model, result);
        }
        else if(expr->isIsEven()){
            return evaluateIsEven(expr, model, result);
        }
        else if(expr->isIsOdd()){
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
        else if(expr->isBvNot()){
            return evaluateBvNot(expr, model, result);
        }
        else if(expr->isBvNeg()){
            return evaluateBvNeg(expr, model, result);
        }
        else if(expr->isBvAnd()){
            return evaluateBvAnd(expr, model, result);
        }
        else if(expr->isBvOr()){
            return evaluateBvOr(expr, model, result);
        }
        else if(expr->isBvXor()){
            return evaluateBvXor(expr, model, result);
        }
        else if(expr->isBvNand()){
            return evaluateBvNand(expr, model, result);
        }
        else if(expr->isBvNor()){
            return evaluateBvNor(expr, model, result);
        }
        else if(expr->isBvXnor()){
            return evaluateBvXnor(expr, model, result);
        }
        else if(expr->isBvComp()){
            return evaluateBvComp(expr, model, result);
        }
        else if(expr->isBvAdd()){
            return evaluateBvAdd(expr, model, result);
        }
        else if(expr->isBvSub()){
            return evaluateBvSub(expr, model, result);
        }
        else if(expr->isBvMul()){
            return evaluateBvMul(expr, model, result);
        }
        else if(expr->isBvUdiv()){
            return evaluateBvUdiv(expr, model, result);
        }
        else if(expr->isBvUrem()){
            return evaluateBvUrem(expr, model, result);
        }
        else if(expr->isBvSdiv()){
            return evaluateBvSdiv(expr, model, result);
        }
        else if(expr->isBvSrem()){
            return evaluateBvSrem(expr, model, result);
        }
        else if(expr->isBvSmod()){
            return evaluateBvSmod(expr, model, result);
        }
        else if(expr->isBvShl()){
            return evaluateBvShl(expr, model, result);
        }
        else if(expr->isBvLshr()){
            return evaluateBvLshr(expr, model, result);
        }
        else if(expr->isBvAshr()){
            return evaluateBvAshr(expr, model, result);
        }
        else if(expr->isBvUlt()){
            return evaluateBvUlt(expr, model, result);
        }
        else if(expr->isBvUle()){
            return evaluateBvUle(expr, model, result);
        }
        else if(expr->isBvUgt()){
            return evaluateBvUgt(expr, model, result);
        }
        else if(expr->isBvUge()){
            return evaluateBvUge(expr, model, result);
        }
        else if(expr->isBvSlt()){
            return evaluateBvSlt(expr, model, result);
        }
        else if(expr->isBvSle()){
            return evaluateBvSle(expr, model, result);
        }
        else if(expr->isBvSgt()){
            return evaluateBvSgt(expr, model, result);
        }
        else if(expr->isBvSge()){
            return evaluateBvSge(expr, model, result);
        }
        else if(expr->isBvConcat()){
            return evaluateBvConcat(expr, model, result);
        }
        else if(expr->isBvToNat()){
            return evaluateBvToNat(expr, model, result);
        }
        else if(expr->isNatToBv()){
            return evaluateNatToBv(expr, model, result);
        }
        else if(expr->isIntToBv()){
            return evaluateIntToBv(expr, model, result);
        }
        else if(expr->isBvToInt()){
            return evaluateBvToInt(expr, model, result);
        }
        else if(expr->isFpAbs()){
            return evaluateFpAbs(expr, model, result);
        }
        else if(expr->isFpNeg()){
            return evaluateFpNeg(expr, model, result);
        }
        else if(expr->isFpAdd()){
            return evaluateFpAdd(expr, model, result);
        }
        else if(expr->isFpSub()){
            return evaluateFpSub(expr, model, result);
        }
        else if(expr->isFpMul()){
            return evaluateFpMul(expr, model, result);
        }
        else if(expr->isFpDiv()){
            return evaluateFpDiv(expr, model, result);
        }
        else if(expr->isFpFma()){
            return evaluateFpFma(expr, model, result);
        }
        else if(expr->isFpSqrt()){
            return evaluateFpSqrt(expr, model, result);
        }
        else if(expr->isFpRem()){
            return evaluateFpRem(expr, model, result);
        }
        else if(expr->isFpRoundToIntegral()){
            return evaluateFpRoundToIntegral(expr, model, result);
        }
        else if(expr->isFpMin()){
            return evaluateFpMin(expr, model, result);
        }
        else if(expr->isFpMax()){
            return evaluateFpMax(expr, model, result);
        }
        else if(expr->isFpLe()){
            return evaluateFpLe(expr, model, result);
        }
        else if(expr->isFpLt()){
            return evaluateFpLt(expr, model, result);
        }
        else if(expr->isFpGe()){
            return evaluateFpGe(expr, model, result);
        }
        else if(expr->isFpGt()){
            return evaluateFpGt(expr, model, result);
        }
        else if(expr->isFpEq()){
            return evaluateFpEq(expr, model, result);
        }
        else if(expr->isFpToUbv()){
            return evaluateFpToUbv(expr, model, result);
        }
        else if(expr->isFpToSbv()){
            return evaluateFpToSbv(expr, model, result);
        }
        else if(expr->isFpToReal()){
            return evaluateFpToReal(expr, model, result);
        }
        else if(expr->isToFp()){
            return evaluateToFp(expr, model, result);
        }
        else if(expr->isFpIsNormal()){
            return evaluateFpIsNormal(expr, model, result);
        }
        else if(expr->isFpIsSubnormal()){
            return evaluateFpIsSubnormal(expr, model, result);
        }
        else if(expr->isFpIsZero()){
            return evaluateFpIsZero(expr, model, result);
        }
        else if(expr->isFpIsInf()){
            return evaluateFpIsInf(expr, model, result);
        }
        else if(expr->isFpIsNan()){
            return evaluateFpIsNan(expr, model, result);
        }
        else if(expr->isFpIsNeg()){
            return evaluateFpIsNeg(expr, model, result);
        }
        else if(expr->isFpIsPos()){
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
        else if(expr->isRegNone()){
            return evaluateRegNone(expr, model, result);
        }
        else if(expr->isRegAll()){
            return evaluateRegAll(expr, model, result);
        }
        else if(expr->isRegAllChar()){
            return evaluateRegAllChar(expr, model, result);
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
            return evaluateFuncApply(expr, model, result);
        }

        return UNKNOWN_NODE;
    }

    bool evaluateSingleOp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result, NODE_KIND op){
        bool changed = false;
        switch(op){
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
            case NODE_KIND::NT_IMPLIES:
            case NODE_KIND::NT_ATAN2:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_GCD:
            case NODE_KIND::NT_LCM:
            case NODE_KIND::NT_BV_ULT:
            case NODE_KIND::NT_BV_ULE:
            case NODE_KIND::NT_BV_UGT:
            case NODE_KIND::NT_BV_UGE:
            case NODE_KIND::NT_BV_SLT:
            case NODE_KIND::NT_BV_SGT:
            case NODE_KIND::NT_BV_SLE:
            case NODE_KIND::NT_BV_SGE:{
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
            case NODE_KIND::NT_IAND:{
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
                    if(children.size() == 1){
                        result = children[0];
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
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_NOT);
    }
    bool Parser::evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IMPLIES);
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
        reuturn true;
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
    
    bool evaluateAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
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
            result = mkAdd(non_const_children);
        }
        else{
            // compute the sum of the constant children
            if(expr->isInt()){
                result = mkInt(0);
                for(auto child : const_children){
                    result = mkAdd(result, child);
                }
            }
            else{
                result = mkReal(0);
                for(auto child : const_children){
                    result = mkAdd(result, child);
                }
            }
            // add the non-constant children to the result
            non_const_children.emplace_back(result);
            result = mkAdd(non_const_children);
        }
        return true; 
    }
    bool evaluateSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
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
            if(expr->isInt()){
                result = mkInt(0);
                for(auto child : const_children){
                    result = mkSub(result, child);
                }
            }
            else{
                result = mkReal(0);
                for(auto child : const_children){
                    result = mkSub(result, child);
                }
            }
            if(first_child_is_const){
                // add the result to the front of the non_const_children
                non_const_children.insert(non_const_children.begin(), result);
            }
            else{
                // add the result to the back of the const_children
                const_children.emplace_back(result);
            }
            result = mkSub(non_const_children);
        }
        return true;
	}
    bool evaluateMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
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
        // compute the product of the children that are constant
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
            result = mkMul(non_const_children);
        }
        else{
            if(expr->isInt()){
                result = mkInt(1);
                for(auto child : const_children){
                    result = mkMul(result, child);
                }
                if(result->isZero()){
                    result = mkInt(0);
                    return true;
                }
            }
            else{
                result = mkReal(1);
                for(auto child : const_children){
                    result = mkMul(result, child);
                }
                if(result->isZero()){
                    result = mkReal(0);
                    return true;
                }
            }
            non_const_children.emplace_back(result);
            result = mkMul(non_const_children);
        }
        return true;
	}
    bool evaluateDivInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
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
            result = mkDiv(non_const_children);
        }
        else{
            if(first_child_is_const){
                auto res = mkInt(1);
                for(size_t i = 1; i < const_children.size(); ++i){
                    res = mkMul(res, const_children[i]);
                }
                if(res->toInt() > const_children[0]->toInt()){
                    // 1 / 3 is 0 in integer arithmetic
                    result = mkInt(0);
                    return true;
                }
                else{
                    // 5 / 3 is 1 in integer arithmetic
                    auto div = mkDivInt(const_children[0], res);
                    non_const_children.insert(non_const_children.begin(), div);
                }
            }
            else{
                auto res = mkInt(1);
                for(size_t i = 0; i < const_children.size(); ++i){
                    res = mkMul(res, const_children[i]);
                }
                non_const_children.emplace_back(res);
                result = mkDiv(non_const_children);
            }
        }
        return true;
	}
    bool evaluateDivReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
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
            result = mkDiv(non_const_children);
        }
        else{
            if(first_child_is_const){
                auto res = mkReal(1);
                for(size_t i = 1; i < const_children.size(); ++i){
                    res = mkMul(res, const_children[i]);
                }
                auto div = mkDivReal(const_children[0], res);
                non_const_children.insert(non_const_children.begin(), div);
            }
            else{
                auto res = mkReal(1);
                for(size_t i = 0; i < const_children.size(); ++i){
                    res = mkMul(res, const_children[i]);
                }
                non_const_children.emplace_back(res);
                result = mkDiv(non_const_children);
            }
        }
        return true;
	}   
    bool evaluateMod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_MOD);
	}
    bool evaluatePow(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_POW);
    }
    bool evaluatePow2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_POW2);
	}
    bool evaluateIand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IAND);
    }
    bool evaluateAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ABS);
	}
    bool evaluateSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_SQRT);
	}
    bool evaluateSafeSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_SAFESQRT);
	}
    bool evaluateCeil(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_CEIL);
	}
    bool evaluateFloor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_FLOOR);
	}
    bool evaluateRound(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ROUND);
	}
    bool evaluateExp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_EXP);
	}
    bool evaluateLn(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_LN);
	}
    bool evaluateLg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_LG);
	}
    bool evaluateSin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_SIN);
	}
    bool evaluateCos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_COS);
	}
    bool evaluateTan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_TAN);
	}
    bool evaluateAsin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ASIN);
	}
    bool evaluateAcos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ACOS);
	}
    bool evaluateAtan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ATAN);
	}
    bool evaluateSinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_SINH);
	}
    bool evaluateCosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_COSH);
	}
    bool evaluateTanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_TANH);
	}
    bool evaluateAsinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ASINH);
	}
    bool evaluateAcosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ACOSH);
	}
    bool evaluateAtanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ATANH);
	}
    bool evaluateAsech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ASECH);
	}
    bool evaluateAcsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ACSCH);
	}
    bool evaluateAcoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ACOTH);
	}
    bool evaluateAtan2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_ATAN2);
	}
    bool evaluateLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_LE);
	}
    bool evaluateLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_LT);
	}
    bool evaluateGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_GE);
	}
    bool evaluateGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_GT);
	}
    bool evaluateToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_TO_REAL);
	}
    bool evaluateToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_TO_INT);
	}
    bool evaluateIsInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IS_INT);
	}
    bool evaluateIsDivisible(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IS_DIVISIBLE);
	}
    bool evaluateIsPrime(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IS_PRIME);
	}
    bool evaluateIsEven(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IS_EVEN);
	}
    bool evaluateIsOdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_IS_ODD);
	}
    bool evaluateGcd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_GCD);
	}
    bool evaluateLcm(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_LCM);
	}
    bool evaluateFact(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_FACT);
	}
    bool evaluateBvNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_NOT);
	}
    bool evaluateBvNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_NEG);
	}
    bool evaluateBvAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_AND);
	}
    bool evaluateBvOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_OR);
	}
    bool evaluateBvXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_XOR);
	}
    bool evaluateBvNand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_NAND);
	}
    bool evaluateBvNor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_NOR);
	}
    bool evaluateBvXnor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_XNOR);
	}
    bool evaluateBvComp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_COMP);
	}
    bool evaluateBvAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_ADD);
	}
    bool evaluateBvSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSingleOp(expr, model, result, NODE_KIND::NT_BV_SUB);
	}
    bool evaluateBvMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSmod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvShl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvLshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvAshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvUge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvSge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvToNat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvNatToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvIntToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateBvToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpDiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpFma(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpRem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpRoundToIntegral(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpToUbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpToSbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateToFp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsNormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsSubnormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsZero(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsInf(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsNan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateFpIsPos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateSelect(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStore(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrLen(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrSubstr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrPrefixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrSuffixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrIndexof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrCharat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrUpdate(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrReplace(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrReplaceAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrToLower(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrToUpper(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrRev(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrSplit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrInReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrContains(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrIsDigit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrFromInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrToReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrToCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateStrFromCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegNone(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegAllChar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegUnion(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegInter(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegDiff(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegStar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegPlus(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegOpt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegRange(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateRegComplement(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
    bool evaluateApplyFun(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
	}
}


