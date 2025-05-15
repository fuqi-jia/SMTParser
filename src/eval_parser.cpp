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
            return true;
        }
        else if(children.size() == 1){
            result = children[0];
            return true;
        }
        else{
            result = mkAnd(children);
            return true;
        }
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
            return true;
        }
        else if(children.size() == 1){
            result = children[0];
            return true;
        }
        else{
            result = mkOr(children);
            return true;
        }
    }
    bool Parser::evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        auto op = NULL_NODE;
        changed |= evaluate(expr->getChild(0), model, op);
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
    bool Parser::evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        auto l = NULL_NODE;
        auto r = NULL_NODE;
        changed |= evaluate(expr->getChild(0), model, l);
        changed |= evaluate(expr->getChild(1), model, r);
        if(!changed){
            result = expr;
            return false;
        }
        assert(changed);
        if(l->isConst() && r->isConst()){
            result = l->isTrue() ? r : mkImpl(l, r);
            return true;
        }
        else{
            result = mkImpl(l, r);
            return true;
        }
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
            return const_val->isTrue() ? mkTrue() : mkFalse();
        }
        else if(children.size() == 1){
            assert(!const_val->isNull());
            result = mkEq(children[0], const_val);
            return true;
        }
        else{
            if(const_val->isNull()){
                result = mkEq(children);
                return true;
            }
            else{
                children.emplace_back(const_val);
                result = mkEq(children);
                return true;
            }
        }
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
            return true;
        }
        else{
            children.insert(children.end(), const_vals.begin(), const_vals.end());
            result = mkDistinct(children);
            return true;
        }
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
            return true;
        }
        else{
            result = mkIte(cond, then_child, else_child);
            return true;
        }
    }
    
}


