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
        if(model->isEmpty()){
            return expr;
        }
        if(expr->isUnknown()){
            return UNKNOWN_NODE;
        }
        else if(expr->isError()){
            return ERROR_NODE;
        }
        else if(expr->isConst()){
            return expr;
        }
        else if(expr->isVar()){
            return model->get(expr)->isUnknown() ? UNKNOWN_NODE : expr;
        }
        else if(expr->isAnd()){
            return evaluateAnd(expr, model);
        }
        else if(expr->isOr()){
            return evaluateOr(expr, model);
        }
        else if(expr->isNot()){
            return evaluateNot(expr, model);
        }
        else if(expr->isImpl()){
            return evaluateImpl(expr, model);
        }
        else if(expr->isXor()){
            return evaluateXor(expr, model);
        }
        else if(expr->isEq()){
            return evaluateEq(expr, model);
        }
        else if(expr->isDistinct()){
            return evaluateDistinct(expr, model);
        }
        else if(expr->isIte()){
            return evaluateIte(expr, model);
        }
        else if(expr->isAdd()){
            return evaluateAdd(expr, model);
        }
        else if(expr->isSub()){
            return evaluateSub(expr, model);
        }
        else if(expr->isMul()){
            return evaluateMul(expr, model);
        }
        else if(expr->isDivInt()){
            return evaluateDivInt(expr, model);
        }
        else if(expr->isDivReal()){
            return evaluateDivReal(expr, model);
        }
        else if(expr->isMod()){
            return evaluateMod(expr, model);
        }
        else if(expr->isPow()){
            return evaluatePow(expr, model);
        }
        else if(expr->isPow2()){
            return evaluatePow2(expr, model);
        }
        else if(expr->isAbs()){
            return evaluateAbs(expr, model);
        }
        else if(expr->isSqrt()){
            return evaluateSqrt(expr, model);
        }
        else if(expr->isSafeSqrt()){
            return evaluateSafeSqrt(expr, model);
        }
        else if(expr->isCeil()){
            return evaluateCeil(expr, model);
        }
        else if(expr->isFloor()){
            return evaluateFloor(expr, model);
        }
        else if(expr->isRound()){
            return evaluateRound(expr, model);
        }
        else if(expr->isExp()){
            return evaluateExp(expr, model);
        }
        else if(expr->isLn()){
            return evaluateLn(expr, model);
        }
        else if(expr->isLg()){
            return evaluateLg(expr, model);
        }
        else if(expr->isLn()){
            return evaluateLn(expr, model);
        }
        else if(expr->isLog()){
            return evaluateLog(expr, model);
        }
        else if(expr->isSin()){
            return evaluateSin(expr, model);
        }
        else if(expr->isCos()){
            return evaluateCos(expr, model);
        }
        else if(expr->isTan()){
            return evaluateTan(expr, model);
        }
        else if(expr->isAsin()){
            return evaluateAsin(expr, model);
        }
        else if(expr->isAcos()){
            return evaluateAcos(expr, model);
        }
        else if(expr->isAtan()){
            return evaluateAtan(expr, model);
        }
        else if(expr->isSinh()){
            return evaluateSinh(expr, model);
        }
        else if(expr->isCosh()){
            return evaluateCosh(expr, model);
        }
        else if(expr->isTanh()){
            return evaluateTanh(expr, model);
        }
        else if(expr->isAsinh()){
            return evaluateAsinh(expr, model);
        }
        else if(expr->isAcosh()){
            return evaluateAcosh(expr, model);
        }
        else if(expr->isAtanh()){
            return evaluateAtanh(expr, model);
        }
        else if(expr->isAsech()){
            return evaluateAsech(expr, model);
        }
        else if(expr->isAcsch()){
            return evaluateAcsch(expr, model);
        }
        else if(expr->isAcoth()){
            return evaluateAcoth(expr, model);
        }
        else if(expr->isAtan2()){
            return evaluateAtan2(expr, model);
        }
        else if(expr->isLe()){
            return evaluateLe(expr, model);
        }
        else if(expr->isLt()){
            return evaluateLt(expr, model);
        }
        else if(expr->isGe()){
            return evaluateGe(expr, model);
        }
        else if(expr->isGt()){
            return evaluateGt(expr, model);
        }
        else if(expr->isToReal()){
            return evaluateToReal(expr, model);
        }
        else if(expr->isToInt()){
            return evaluateToInt(expr, model);
        }
        else if(expr->isIsInt()){
            return evaluateIsInt(expr, model);
        }
        else if(expr->isIsDivisible()){
            return evaluateIsDivisible(expr, model);
        }
        else if(expr->isIsPrime()){
            return evaluateIsPrime(expr, model);
        }
        else if(expr->isIsEven()){
            return evaluateIsEven(expr, model);
        }
        else if(expr->isIsOdd()){
            return evaluateIsOdd(expr, model);
        }
        else if(expr->isGcd()){
            return evaluateGcd(expr, model);
        }
        else if(expr->isLcm()){
            return evaluateLcm(expr, model);
        }
        else if(expr->isFact()){
            return evaluateFact(expr, model);
        }
        else if(expr->isBvNot()){
            return evaluateBvNot(expr, model);
        }
        else if(expr->isBvNeg()){
            return evaluateBvNeg(expr, model);
        }
        else if(expr->isBvAnd()){
            return evaluateBvAnd(expr, model);
        }
        else if(expr->isBvOr()){
            return evaluateBvOr(expr, model);
        }
        else if(expr->isBvXor()){
            return evaluateBvXor(expr, model);
        }
        else if(expr->isBvNand()){
            return evaluateBvNand(expr, model);
        }
        else if(expr->isBvNor()){
            return evaluateBvNor(expr, model);
        }
        else if(expr->isBvXnor()){
            return evaluateBvXnor(expr, model);
        }
        else if(expr->isBvComp()){
            return evaluateBvComp(expr, model);
        }
        else if(expr->isBvAdd()){
            return evaluateBvAdd(expr, model);
        }
        else if(expr->isBvSub()){
            return evaluateBvSub(expr, model);
        }
        else if(expr->isBvMul()){
            return evaluateBvMul(expr, model);
        }
        else if(expr->isBvUdiv()){
            return evaluateBvUdiv(expr, model);
        }
        else if(expr->isBvUrem()){
            return evaluateBvUrem(expr, model);
        }
        else if(expr->isBvSdiv()){
            return evaluateBvSdiv(expr, model);
        }
        else if(expr->isBvSrem()){
            return evaluateBvSrem(expr, model);
        }
        else if(expr->isBvSmod()){
            return evaluateBvSmod(expr, model);
        }
        else if(expr->isBvShl()){
            return evaluateBvShl(expr, model);
        }
        else if(expr->isBvLshr()){
            return evaluateBvLshr(expr, model);
        }
        else if(expr->isBvAshr()){
            return evaluateBvAshr(expr, model);
        }
        else if(expr->isBvUlt()){
            return evaluateBvUlt(expr, model);
        }
        else if(expr->isBvUle()){
            return evaluateBvUle(expr, model);
        }
        else if(expr->isBvUgt()){
            return evaluateBvUgt(expr, model);
        }
        else if(expr->isBvUge()){
            return evaluateBvUge(expr, model);
        }
        else if(expr->isBvSlt()){
            return evaluateBvSlt(expr, model);
        }
        else if(expr->isBvSle()){
            return evaluateBvSle(expr, model);
        }
        else if(expr->isBvSgt()){
            return evaluateBvSgt(expr, model);
        }
        else if(expr->isBvSge()){
            return evaluateBvSge(expr, model);
        }
        else if(expr->isBvConcat()){
            return evaluateBvConcat(expr, model);
        }
        else if(expr->isBvToNat()){
            return evaluateBvToNat(expr, model);
        }
        else if(expr->isNatToBv()){
            return evaluateNatToBv(expr, model);
        }
        else if(expr->isIntToBv()){
            return evaluateIntToBv(expr, model);
        }
        else if(expr->isBvToInt()){
            return evaluateBvToInt(expr, model);
        }
        else if(expr->isFpAbs()){
            return evaluateFpAbs(expr, model);
        }
        else if(expr->isFpNeg()){
            return evaluateFpNeg(expr, model);
        }
        else if(expr->isFpAdd()){
            return evaluateFpAdd(expr, model);
        }
        else if(expr->isFpSub()){
            return evaluateFpSub(expr, model);
        }
        else if(expr->isFpMul()){
            return evaluateFpMul(expr, model);
        }
        else if(expr->isFpDiv()){
            return evaluateFpDiv(expr, model);
        }
        else if(expr->isFpFma()){
            return evaluateFpFma(expr, model);
        }
        else if(expr->isFpSqrt()){
            return evaluateFpSqrt(expr, model);
        }
        else if(expr->isFpRem()){
            return evaluateFpRem(expr, model);
        }
        else if(expr->isFpRoundToIntegral()){
            return evaluateFpRoundToIntegral(expr, model);
        }
        else if(expr->isFpMin()){
            return evaluateFpMin(expr, model);
        }
        else if(expr->isFpMax()){
            return evaluateFpMax(expr, model);
        }
        else if(expr->isFpLe()){
            return evaluateFpLe(expr, model);
        }
        else if(expr->isFpLt()){
            return evaluateFpLt(expr, model);
        }
        else if(expr->isFpGe()){
            return evaluateFpGe(expr, model);
        }
        else if(expr->isFpGt()){
            return evaluateFpGt(expr, model);
        }
        else if(expr->isFpEq()){
            return evaluateFpEq(expr, model);
        }
        else if(expr->isFpToUbv()){
            return evaluateFpToUbv(expr, model);
        }
        else if(expr->isFpToSbv()){
            return evaluateFpToSbv(expr, model);
        }
        else if(expr->isFpToReal()){
            return evaluateFpToReal(expr, model);
        }
        else if(expr->isToFp()){
            return evaluateToFp(expr, model);
        }
        else if(expr->isFpIsNormal()){
            return evaluateFpIsNormal(expr, model);
        }
        else if(expr->isFpIsSubnormal()){
            return evaluateFpIsSubnormal(expr, model);
        }
        else if(expr->isFpIsZero()){
            return evaluateFpIsZero(expr, model);
        }
        else if(expr->isFpIsInf()){
            return evaluateFpIsInf(expr, model);
        }
        else if(expr->isFpIsNan()){
            return evaluateFpIsNan(expr, model);
        }
        else if(expr->isFpIsNeg()){
            return evaluateFpIsNeg(expr, model);
        }
        else if(expr->isFpIsPos()){
            return evaluateFpIsPos(expr, model);
        }
        else if(expr->isSelect()){
            return evaluateSelect(expr, model);
        }
        else if(expr->isStore()){
            return evaluateStore(expr, model);
        }
        else if(expr->isStrLen()){
            return evaluateStrLen(expr, model);
        }
        else if(expr->isStrConcat()){
            return evaluateStrConcat(expr, model);
        }
        else if(expr->isStrSubstr()){
            return evaluateStrSubstr(expr, model);
        }
        else if(expr->isStrPrefixof()){
            return evaluateStrPrefixof(expr, model);
        }
        else if(expr->isStrSuffixof()){
            return evaluateStrSuffixof(expr, model);
        }
        else if(expr->isStrIndexof()){
            return evaluateStrIndexof(expr, model);
        }
        else if(expr->isStrCharat()){
            return evaluateStrCharat(expr, model);
        }
        else if(expr->isStrUpdate()){
            return evaluateStrUpdate(expr, model);
        }
        else if(expr->isStrReplace()){
            return evaluateStrReplace(expr, model);
        }
        else if(expr->isStrReplaceAll()){
            return evaluateStrReplaceAll(expr, model);
        }
        else if(expr->isStrToLower()){
            return evaluateStrToLower(expr, model);
        }
        else if(expr->isStrToUpper()){
            return evaluateStrToUpper(expr, model);
        }
        else if(expr->isStrRev()){
            return evaluateStrRev(expr, model);
        }
        else if(expr->isStrSplit()){
            return evaluateStrSplit(expr, model);
        }
        else if(expr->isStrLt()){
            return evaluateStrLt(expr, model);
        }
        else if(expr->isStrLe()){
            return evaluateStrLe(expr, model);
        }
        else if(expr->isStrGt()){
            return evaluateStrGt(expr, model);
        }
        else if(expr->isStrGe()){
            return evaluateStrGe(expr, model);
        }
        else if(expr->isStrInReg()){
            return evaluateStrInReg(expr, model);
        }
        else if(expr->isStrContains()){
            return evaluateStrContains(expr, model);
        }
        else if(expr->isStrIsDigit()){
            return evaluateStrIsDigit(expr, model);
        }
        else if(expr->isStrFromInt()){
            return evaluateStrFromInt(expr, model);
        }
        else if(expr->isStrToInt()){
            return evaluateStrToInt(expr, model);
        }
        else if(expr->isStrToReg()){
            return evaluateStrToReg(expr, model);
        }
        else if(expr->isStrToCode()){
            return evaluateStrToCode(expr, model);
        }
        else if(expr->isStrFromCode()){
            return evaluateStrFromCode(expr, model);
        }
        else if(expr->isRegNone()){
            return evaluateRegNone(expr, model);
        }
        else if(expr->isRegAll()){
            return evaluateRegAll(expr, model);
        }
        else if(expr->isRegAllChar()){
            return evaluateRegAllChar(expr, model);
        }
        else if(expr->isRegConcat()){
            return evaluateRegConcat(expr, model);
        }
        else if(expr->isRegUnion()){
            return evaluateRegUnion(expr, model);
        }
        else if(expr->isRegInter()){
            return evaluateRegInter(expr, model);
        }
        else if(expr->isRegDiff()){
            return evaluateRegDiff(expr, model);
        }
        else if(expr->isRegStar()){
            return evaluateRegStar(expr, model);
        }
        else if(expr->isRegPlus()){
            return evaluateRegPlus(expr, model);
        }
        else if(expr->isRegOpt()){
            return evaluateRegOpt(expr, model);
        }
        else if(expr->isRegRange()){
            return evaluateRegRange(expr, model);
        }
        else if(expr->isRegRepeat()){
            return evaluateRegRepeat(expr, model);
        }
        else if(expr->isRegComplement()){
            return evaluateRegComplement(expr, model);
        }
        else if(expr->isFuncApply()){
            return evaluateFuncApply(expr, model);
        }

        return UNKNOWN_NODE;
    }

    std::shared_ptr<DAGNode> Parser::evaluateAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        std::vector<std::shared_ptr<DAGNode>> children;
        for(auto child : expr->getChildren()){
            auto eval = evaluate(child, model);
            if(eval->isUnknown()){
                return UNKNOWN_NODE;
            }
            else if(eval->isConst()){
                if(eval->isFalse()){
                    return mkFalse();
                }
            }
            else{
                children.push_back(eval);
            }
        }
        if(children.empty()){
            return mkTrue();
        }
        else if(children.size() == 1){
            return children[0];
        }
        else{
            return mkAnd(children);
        }
    }
    std::shared_ptr<DAGNode> Parser::evaluateOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        std::vector<std::shared_ptr<DAGNode>> children;
        for(auto child : expr->getChildren()){
            auto eval = evaluate(child, model);
            if(eval->isUnknown()){
                return UNKNOWN_NODE;
            }
            else if(eval->isConst()){
                if(eval->isTrue()){
                    return mkTrue();
                }
            }
            else{
                children.push_back(eval);
            }
        }
        if(children.empty()){
            return mkFalse();
        }
        else if(children.size() == 1){
            return children[0];
        }
        else{
            return mkOr(children);
        }
    }
    std::shared_ptr<DAGNode> Parser::evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        auto op = evaluate(expr->getChild(0), model);
        if(op->isUnknown()){
            return UNKNOWN_NODE;
        }
        else if(op->isConst()){
            return op->isTrue() ? mkFalse() : mkTrue();
        }
        else{
            return mkNot(op);
        }
    }
    std::shared_ptr<DAGNode> Parser::evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        auto l = evaluate(expr->getChild(0), model);
        auto r = evaluate(expr->getChild(1), model);
        if(l->isUnknown() || r->isUnknown()){
            return UNKNOWN_NODE;
        }
        return mkImpl(l, r);
    }
    std::shared_ptr<DAGNode> Parser::evaluateXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        // count true
        size_t trueCount = 0;
        // save unevaluated children
        std::vector<std::shared_ptr<DAGNode>> remainingChildren;
        
        // traverse all children
        for (auto child : expr->getChildren()) {
            auto evaluatedChild = evaluate(child, model);
            
            // cannot evaluate
            if (evaluatedChild->isUnknown()) {
                return UNKNOWN_NODE;
            }
            
            // evaluated as constant
            if (evaluatedChild->isConst()) {
                if (evaluatedChild->isTrue()) {
                    trueCount++;
                }
                // ignore false
            } else {
                // save unevaluated children
                remainingChildren.push_back(evaluatedChild);
            }
        }
        
        // all children are constants
        if (remainingChildren.empty()) {
            // result depends on true count is odd or even
            return (trueCount % 2 == 1) ? mkTrue() : mkFalse();
        }
        
        // only one unevaluated child
        if (remainingChildren.size() == 1) {
            // if true count is even, result is the child
            // if true count is odd, result is the negation of the child
            return (trueCount % 2 == 0) ? 
                   remainingChildren[0] : 
                   mkNot(remainingChildren[0]);
        }
        
        // multiple unevaluated children
        // decide return XOR or its negation based on true count
        if (trueCount % 2 == 0) {
            return mkXor(remainingChildren);
        } else {
            return mkNot(mkXor(remainingChildren));
        }
    }
    std::shared_ptr<DAGNode> Parser::evaluateEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        std::vector<std::shared_ptr<DAGNode>> children;
        std::shared_ptr<DAGNode> const_val = NULL_NODE;
        for(auto child : expr->getChildren()){
            auto eval = evaluate(child, model);
            if(eval->isUnknown()){
                return UNKNOWN_NODE;
            }
            else if(eval->isConst()){
                if(const_val == NULL_NODE){
                    const_val = eval;
                }
                else if(const_val->toString() != eval->toString()){
                    return mkFalse();
                }
            }
            else{
                children.push_back(eval);
            }
        }
        if(children.empty()){
            return const_val->isTrue() ? mkTrue() : mkFalse();
        }
        else if(children.size() == 1){
            assert(!const_val->isNull());
            return mkEq(children[0], const_val);
        }
        else{
            if(const_val->isNull()){
                return mkEq(children);
            }
            else{
                children.push_back(const_val);
                return mkEq(children);
            }
        }
        return UNKNOWN_NODE;
    }
    std::shared_ptr<DAGNode> Parser::evaluateDistinct(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        std::vector<std::shared_ptr<DAGNode>> children;
        boost::unordered_set<std::shared_ptr<DAGNode>> const_vals;
        for(auto child : expr->getChildren()){
            auto eval = evaluate(child, model);
            if(eval->isUnknown()){
                return UNKNOWN_NODE;
            }
            else if(eval->isConst()){
                if(const_vals.empty()){
                    const_vals.insert(eval);
                }
                else if(const_vals.find(eval) == const_vals.end()){
                    const_vals.insert(eval);
                }
                else{
                    return mkFalse();
                }
            }
            else{
                children.push_back(eval);
            }
        }
        if(children.empty()){
            assert(const_vals.size() == expr->getChildrenSize());
            return mkTrue();
        }
        else{
            children.   (children.end(), const_vals.begin(), const_vals.end());
            return mkDistinct(children);
        }
    }
    std::shared_ptr<DAGNode> Parser::evaluateIte(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model) {
        auto cond = evaluate(expr->getChild(0), model);
        if(cond->isUnknown()){
            return UNKNOWN_NODE;
        }
        
    }
}


