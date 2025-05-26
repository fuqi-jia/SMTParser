/* -*- Source -*-
 *
 * The SMT Interval Source
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

#include "smt_interval.h"

namespace SMTLIBParser{

    SMTInterval::SMTInterval(std::shared_ptr<Parser> parser, std::shared_ptr<DAGNode> lower, std::shared_ptr<DAGNode> upper, std::shared_ptr<DAGNode> leftClosed, std::shared_ptr<DAGNode> rightClosed)
        : parser(parser), lower(lower), upper(upper), leftClosed(leftClosed), rightClosed(rightClosed) {}

    SMTInterval::SMTInterval(std::shared_ptr<Parser> parser, const Interval& interval){
        this->parser = parser;
        this->lower = parser->mkConstReal(interval.getLower());
        this->upper = parser->mkConstReal(interval.getUpper());
        this->leftClosed = interval.isLeftClosed() ? parser->mkTrue() : parser->mkFalse();
        this->rightClosed = interval.isRightClosed() ? parser->mkTrue() : parser->mkFalse();
    }
    SMTInterval::SMTInterval(const SMTInterval& other)
        : parser(other.parser), lower(other.lower), upper(other.upper), leftClosed(other.leftClosed), rightClosed(other.rightClosed) {}

    SMTInterval::~SMTInterval() {}

    SMTInterval& SMTInterval::operator=(const SMTInterval& other) {
        if(this != &other) {
            parser = other.parser;
            lower = other.lower;
            upper = other.upper;
            leftClosed = other.leftClosed;
            rightClosed = other.rightClosed;
        }
        return *this;
    }

    bool SMTInterval::operator==(const SMTInterval& other) const {
        return lower == other.lower && upper == other.upper && leftClosed == other.leftClosed && rightClosed == other.rightClosed;
    }

    bool SMTInterval::operator!=(const SMTInterval& other) const {
        return !(*this == other);
    }

    bool SMTInterval::setLower(std::shared_ptr<DAGNode> lower) {
        lower = lower;
        return true;
    }

    bool SMTInterval::setUpper(std::shared_ptr<DAGNode> upper) {
        upper = upper;
        return true;
    }

    bool SMTInterval::setLeftClosed(std::shared_ptr<DAGNode> leftClosed) {
        leftClosed = leftClosed;
        return true;
    }

    bool SMTInterval::setRightClosed(std::shared_ptr<DAGNode> rightClosed) {
        rightClosed = rightClosed;
        return true;
    }

    bool SMTInterval::setLower(const Number& lower){
        this->lower = parser->mkConstReal(lower);
        return true;
    }
    bool SMTInterval::setUpper(const Number& upper){
        this->upper = parser->mkConstReal(upper);
        return true;
    }
    bool SMTInterval::setLeftClosed(bool leftClosed){
        this->leftClosed = leftClosed ? parser->mkTrue() : parser->mkFalse();
        return true;    
    }
    bool SMTInterval::setRightClosed(bool rightClosed){
        this->rightClosed = rightClosed ? parser->mkTrue() : parser->mkFalse();
        return true;
    }

    std::shared_ptr<DAGNode> SMTInterval::isLeftClosed() const {
        return leftClosed;
    }

    std::shared_ptr<DAGNode> SMTInterval::isRightClosed() const {
        return rightClosed;
    }

    bool SMTInterval::isLeftUnbounded() const {
        return lower->isInfinity();
    }

    bool SMTInterval::isRightUnbounded() const {
        return upper->isInfinity();
    }

    std::shared_ptr<DAGNode> SMTInterval::midpoint() const {
        return parser->mkDiv(parser->mkAdd(lower, upper), parser->mkConstInt(2));
    }
    std::string SMTInterval::toString() const {
        std::stringstream ss;
        if(isLeftClosed() == parser->mkTrue()){
            ss << "[";
        }
        else if(isLeftClosed() == parser->mkFalse()){
            ss << "(";
        }
        else{
            ss << "[(";
        }
        ss << parser->toString(lower) << ", " << parser->toString(upper);
        if(isRightClosed() == parser->mkTrue()){
            ss << "]";
        }
        else if(isRightClosed() == parser->mkFalse()){
            ss << ")";
        }
        else{
            ss << ")]";
        }
        return ss.str();
    }

    std::shared_ptr<DAGNode> SMTInterval::isPoint() const{
        return parser->mkAnd(parser->mkEq(lower, upper), leftClosed, rightClosed);
    }
    std::shared_ptr<DAGNode> SMTInterval::isEmpty() const{
        return parser->mkOr({parser->mkLt(upper, lower), parser->mkAnd(parser->mkEq(lower, upper), parser->mkNot(leftClosed), parser->mkNot(rightClosed))});
    }
    std::shared_ptr<DAGNode> SMTInterval::width() const{
        return parser->mkSub(upper, lower);
    }
    std::shared_ptr<DAGNode> SMTInterval::contains(const std::shared_ptr<DAGNode>& value) const{
        return parser->mkAnd(parser->mkLt(lower, value), parser->mkLt(value, upper));
    }
    std::shared_ptr<DAGNode> SMTInterval::isSubsetOf(const SMTInterval& other) const{
        return parser->mkAnd(
            parser->mkOr({  parser->mkGt(lower, other.lower), 
                            parser->mkAnd({parser->mkEq(lower, other.lower), 
                                           parser->mkOr({parser->mkNot(other.leftClosed), leftClosed})})}),
            parser->mkOr({parser->mkLt(upper, other.upper), 
                         parser->mkAnd({parser->mkEq(upper, other.upper), 
                                        parser->mkOr({parser->mkNot(other.rightClosed), rightClosed})})})
        );
    }
    std::shared_ptr<DAGNode> SMTInterval::isSubsetEqOf(const SMTInterval& other) const{
        return parser->mkOr({
            isSubsetOf(other),
            parser->mkAnd({parser->mkEq(lower, other.lower), parser->mkEq(upper, other.upper), parser->mkEq(leftClosed, other.leftClosed), parser->mkEq(rightClosed, other.rightClosed)})
        });
    }
    std::shared_ptr<DAGNode> SMTInterval::isSupersetOf(const SMTInterval& other) const{
        return other.isSubsetOf(*this);
    }
    std::shared_ptr<DAGNode> SMTInterval::isDisjointFrom(const SMTInterval& other) const{
        return parser->mkOr({
            parser->mkLt(upper, other.lower), 
            parser->mkLt(other.upper, lower),
            parser->mkAnd({parser->mkEq(upper, other.lower), parser->mkOr({parser->mkNot(rightClosed), parser->mkNot(other.leftClosed)})}),
            parser->mkAnd({parser->mkEq(lower, other.upper), parser->mkOr({parser->mkNot(leftClosed), parser->mkNot(other.rightClosed)})})
        });
    }
    std::shared_ptr<DAGNode> SMTInterval::isIntersectingWith(const SMTInterval& other) const{
        return parser->mkNot(isDisjointFrom(other));
    }
    SMTInterval SMTInterval::intersection(const SMTInterval& other) const{
        auto lower_ = parser->mkMax({lower, other.lower});
        auto upper_ = parser->mkMin({upper, other.upper});
        auto leftClosed_ = parser->mkIte(parser->mkLt(lower, other.lower), other.leftClosed, leftClosed);
        auto rightClosed_ = parser->mkIte(parser->mkLt(upper, other.upper), other.rightClosed, rightClosed);
        return SMTInterval(parser, lower_, upper_, leftClosed_, rightClosed_);
    }
    SMTInterval SMTInterval::unionWith(const SMTInterval& other) const{
        // if it is disjoint, it is an over approximation
        auto lower_ = parser->mkMin({lower, other.lower});
        auto upper_ = parser->mkMax({upper, other.upper});
        auto leftClosed_ = parser->mkIte(parser->mkLt(lower, other.lower), other.leftClosed, leftClosed);
        auto rightClosed_ = parser->mkIte(parser->mkLt(upper, other.upper), other.rightClosed, rightClosed);
        return SMTInterval(parser, lower_, upper_, leftClosed_, rightClosed_);
    }
    std::vector<SMTInterval> SMTInterval::difference(const SMTInterval& other) const{
        // TODO: implement this
        (void)other;
        cassert(false, "Not implemented");
        return {};
    }

    // unary operators
    SMTInterval SMTInterval::operator++() const{
        return SMTInterval(parser, parser->mkAdd(lower, parser->mkConstInt(1)), parser->mkAdd(upper, parser->mkConstInt(1)), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::operator--() const{
        return SMTInterval(parser, parser->mkSub(lower, parser->mkConstInt(1)), parser->mkSub(upper, parser->mkConstInt(1)), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::operator-() const{
        return SMTInterval(parser, parser->mkNeg(upper), parser->mkNeg(lower), rightClosed, leftClosed);
    }
    SMTInterval SMTInterval::operator+() const{
        return *this;
    }
    SMTInterval SMTInterval::operator~() const{
        return -*this;
    }
    SMTInterval SMTInterval::operator!() const{
        return -*this;
    }
    SMTInterval SMTInterval::operator++(int) const{
        return SMTInterval(parser, parser->mkAdd(lower, parser->mkConstInt(1)), parser->mkAdd(upper, parser->mkConstInt(1)), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::operator--(int) const{
        return SMTInterval(parser, parser->mkSub(lower, parser->mkConstInt(1)), parser->mkSub(upper, parser->mkConstInt(1)), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::negate() const{
        return -*this;
    }
    SMTInterval SMTInterval::abs() const{
        auto ZERO = parser->mkConstReal(0);
        auto first_condition = parser->mkGe(lower, ZERO);
        auto second_condition = parser->mkLe(upper, ZERO);

        auto lower_ = parser->mkIte( first_condition, 
                                    lower, 
                                    parser->mkIte(second_condition, parser->mkNeg(upper), parser->getZero(lower->getSort())));
        auto abs_max = parser->mkMax({parser->mkAbs(lower), parser->mkAbs(upper)});
        auto upper_ = parser->mkIte( first_condition, 
                                    upper, 
                                    parser->mkIte(second_condition, parser->mkNeg(lower), abs_max));
        auto leftClosed_ = parser->mkIte(first_condition, 
                                        leftClosed, 
                                        parser->mkIte(second_condition, rightClosed, parser->mkTrue()));
        auto rightClosed_ = parser->mkIte(first_condition, 
                                        rightClosed, 
                                        parser->mkIte(second_condition, leftClosed, 
                                                      parser->mkIte(
                                                        parser->mkEq(abs_max, parser->mkAbs(lower)),
                                                        leftClosed,
                                                        rightClosed
                                                      )));
        return SMTInterval(parser, lower_, upper_, leftClosed_, rightClosed_);
    }
    SMTInterval SMTInterval::lb() const{
        return SMTInterval(parser, parser->mkLb(lower), parser->mkLb(upper), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::ln() const{
        return SMTInterval(parser, parser->mkLn(lower), parser->mkLn(upper), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::lg() const{
        return SMTInterval(parser, parser->mkLg(lower), parser->mkLg(upper), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::exp() const{
        return SMTInterval(parser, parser->mkExp(lower), parser->mkExp(upper), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::sqrt() const{
        // auto ZERO = parser->mkConstReal(0);
        // auto condition = parser->mkGe(lower, ZERO);
        // auto error_msg = parser->mkStr("Cannot compute square root of interval containing negative numbers");
        // // assert condition
        // parser->mkIte(condition, parser->mkTrue(), parser->mkError(error_msg));
        // if condition is true, compute sqrt

        // directly compute sqrt
        return SMTInterval(parser, parser->mkSqrt(lower), parser->mkSqrt(upper), leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::safesqrt() const{
        auto ZERO = parser->mkConstReal(0);
        auto condition = parser->mkGe(lower, ZERO);
        auto new_lower = parser->mkIte(condition, parser->mkSqrt(lower), ZERO);
        return SMTInterval(parser, new_lower, parser->mkSqrt(upper), parser->mkIte(condition, leftClosed, parser->mkTrue()), rightClosed);
    }
    SMTInterval SMTInterval::sin() const{
        // define the period
        auto TWO_PI = parser->mkMul(parser->mkConstReal(2), parser->mkPi());
        auto PI_HALF = parser->mkDivReal(parser->mkPi(), parser->mkConstReal(2));
        auto THREE_PI_HALF = parser->mkMul(parser->mkConstReal(3), PI_HALF);
        
        // check if the interval covers the whole period
        auto covers_period = parser->mkGe(parser->mkSub(upper, lower), TWO_PI);
        
        // if the interval covers the whole period, return [-1, 1]
        auto full_range_lower = parser->mkConstInt(-1);
        auto full_range_upper = parser->mkConstInt(1);
        
        // compute the sin value
        auto sin_lower = parser->mkSin(lower);
        auto sin_upper = parser->mkSin(upper);
        
        // determine the min and max value
        auto min_val = parser->mkMin({sin_lower, sin_upper});
        auto max_val = parser->mkMax({sin_lower, sin_upper});
        std::shared_ptr<DAGNode> newLeftClosed = parser->mkIte(parser->mkLe(sin_lower, sin_upper), leftClosed, rightClosed);
        std::shared_ptr<DAGNode> newRightClosed = parser->mkIte(parser->mkLe(sin_lower, sin_upper), rightClosed, leftClosed);
        
        // check if the interval passes π/2 (sin max value is 1)
        auto contains_pi_half = parser->mkAnd(
            parser->mkLe(lower, PI_HALF),
            parser->mkGe(upper, PI_HALF)
        );
        
        // check if the interval passes 3π/2 (sin min value is -1)
        auto contains_three_pi_half = parser->mkAnd(
            parser->mkLe(lower, THREE_PI_HALF),
            parser->mkGe(upper, THREE_PI_HALF)
        );
        
        // if the interval passes π/2, the max value is 1
        max_val = parser->mkIte(contains_pi_half, parser->mkConstInt(1), max_val);
        newLeftClosed = parser->mkIte(contains_pi_half, parser->mkTrue(), newLeftClosed);

        // if the interval passes 3π/2, the min value is -1
        min_val = parser->mkIte(contains_three_pi_half, parser->mkConstInt(-1), min_val);
        newRightClosed = parser->mkIte(contains_three_pi_half, parser->mkTrue(), newRightClosed);
        
        // if the interval covers the whole period, return [-1, 1]
        min_val = parser->mkIte(covers_period, full_range_lower, min_val);
        max_val = parser->mkIte(covers_period, full_range_upper, max_val);
        newLeftClosed = parser->mkIte(covers_period, parser->mkTrue(), newLeftClosed);
        newRightClosed = parser->mkIte(covers_period, parser->mkTrue(), newRightClosed);
        
        // return the result interval
        return SMTInterval(parser, min_val, max_val, newLeftClosed, newRightClosed);
    }
    SMTInterval SMTInterval::cos() const{
        // define the period
        auto TWO_PI = parser->mkMul(parser->mkConstReal(2), parser->mkPi());
        auto PI = parser->mkPi();
        auto ZERO = parser->mkConstReal(0);
        
        // check if the interval covers the whole period
        auto covers_period = parser->mkGe(parser->mkSub(upper, lower), TWO_PI);
        
        // if the interval covers the whole period, return [-1, 1]
        auto full_range_lower = parser->mkConstReal(-1);
        auto full_range_upper = parser->mkConstReal(1);
        
        // compute the cos value
        auto cos_lower = parser->mkCos(lower);
        auto cos_upper = parser->mkCos(upper);
        
        // determine the min and max value
        auto min_val = parser->mkMin({cos_lower, cos_upper});
        auto max_val = parser->mkMax({cos_lower, cos_upper});
        std::shared_ptr<DAGNode> newLeftClosed = parser->mkIte(parser->mkLe(cos_lower, cos_upper), leftClosed, rightClosed);
        std::shared_ptr<DAGNode> newRightClosed = parser->mkIte(parser->mkLe(cos_lower, cos_upper), rightClosed, leftClosed);
        
        // check if the interval passes 0 (cos max value is 1)
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // check if the interval passes π (cos min value is -1)
        auto contains_pi = parser->mkAnd(
            parser->mkLe(lower, PI),
            parser->mkGe(upper, PI)
        );
        
        // if the interval passes 0, the max value is 1
        max_val = parser->mkIte(contains_zero, parser->mkConstReal(1), max_val);
        newLeftClosed = parser->mkIte(contains_zero, parser->mkTrue(), newLeftClosed);
        
        // if the interval passes π, the min value is -1
        min_val = parser->mkIte(contains_pi, parser->mkConstReal(-1), min_val);
        newRightClosed = parser->mkIte(contains_pi, parser->mkTrue(), newRightClosed);
        
        // ensure the interval doesn't exceed the range of cosine function [-1, 1]
        min_val = parser->mkMax({min_val, parser->mkConstReal(-1)});
        max_val = parser->mkMin({max_val, parser->mkConstReal(1)});
        
        // if the interval covers the whole period, return [-1, 1]
        min_val = parser->mkIte(covers_period, full_range_lower, min_val);
        max_val = parser->mkIte(covers_period, full_range_upper, max_val);
        newLeftClosed = parser->mkIte(covers_period, parser->mkTrue(), newLeftClosed);
        newRightClosed = parser->mkIte(covers_period, parser->mkTrue(), newRightClosed);
        
        // return the result interval
        return SMTInterval(parser, min_val, max_val, newLeftClosed, newRightClosed);
    }
    SMTInterval SMTInterval::tan() const{
        // define constants
        auto PI_HALF = parser->mkDivReal(parser->mkPi(), parser->mkConstReal(2));
        auto NEG_PI_HALF = parser->mkNeg(PI_HALF);
        
        // check if the interval contains odd multiples of π/2 (tangent singularities)
        auto contains_singularity = parser->mkOr(
            parser->mkAnd(parser->mkLe(lower, NEG_PI_HALF), parser->mkGe(upper, NEG_PI_HALF)),
            parser->mkAnd(parser->mkLe(lower, PI_HALF), parser->mkGe(upper, PI_HALF))
        );
        
        // if it contains singularities, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // compute tan values
        auto tan_lower = parser->mkTan(lower);
        auto tan_upper = parser->mkTan(upper);
        
        // determine min and max values
        auto min_val = parser->mkMin({tan_lower, tan_upper});
        auto max_val = parser->mkMax({tan_lower, tan_upper});
        std::shared_ptr<DAGNode> newLeftClosed = parser->mkIte(parser->mkLe(tan_lower, tan_upper), leftClosed, rightClosed);
        std::shared_ptr<DAGNode> newRightClosed = parser->mkIte(parser->mkLe(tan_lower, tan_upper), rightClosed, leftClosed);
        
        // if it contains singularities, return (-∞, ∞)
        min_val = parser->mkIte(contains_singularity, neg_inf, min_val);
        max_val = parser->mkIte(contains_singularity, pos_inf, max_val);
        
        // return the result interval
        return SMTInterval(parser, min_val, max_val, 
                          parser->mkIte(contains_singularity, parser->mkFalse(), newLeftClosed),
                          parser->mkIte(contains_singularity, parser->mkFalse(), newRightClosed));
    }
    SMTInterval SMTInterval::cot() const{
        // define constants
        auto PI = parser->mkPi();
        auto ZERO = parser->mkConstReal(0);
        
        // calculate tangent interval
        SMTInterval tan_interval = this->tan();
        
        // check if tan interval contains 0 (cotangent has singularities at these points)
        auto contains_zero = parser->mkOr(
            parser->mkEq(tan_interval.getLower(), ZERO),
            parser->mkEq(tan_interval.getUpper(), ZERO),
            parser->mkAnd(parser->mkLt(tan_interval.getLower(), ZERO), 
                         parser->mkGt(tan_interval.getUpper(), ZERO))
        );
        
        // if contains 0, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // calculate cot values (cot(x) = 1/tan(x))
        auto cot_lower = parser->mkDiv(parser->mkConstReal(1), tan_interval.getUpper());
        auto cot_upper = parser->mkDiv(parser->mkConstReal(1), tan_interval.getLower());
        
        // if contains singularities, return (-∞, ∞)
        auto result_lower = parser->mkIte(contains_zero, neg_inf, cot_lower);
        auto result_upper = parser->mkIte(contains_zero, pos_inf, cot_upper);
        
        // return the result interval
        return SMTInterval(parser, result_lower, result_upper,
                          parser->mkIte(contains_zero, parser->mkFalse(), tan_interval.isRightClosed()),
                          parser->mkIte(contains_zero, parser->mkFalse(), tan_interval.isLeftClosed()));
    }
    SMTInterval SMTInterval::sec() const{
        // calculate cosine interval
        SMTInterval cos_interval = this->cos();
        auto ZERO = parser->mkConstReal(0);
        
        // check if cos interval contains 0 (secant has singularities at these points)
        auto contains_zero = parser->mkOr(
            parser->mkEq(cos_interval.getLower(), ZERO),
            parser->mkEq(cos_interval.getUpper(), ZERO),
            parser->mkAnd(parser->mkLt(cos_interval.getLower(), ZERO), 
                         parser->mkGt(cos_interval.getUpper(), ZERO))
        );
        
        // if contains 0, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // calculate sec values (sec(x) = 1/cos(x))
        auto sec_lower = parser->mkDiv(parser->mkConstReal(1), cos_interval.getUpper());
        auto sec_upper = parser->mkDiv(parser->mkConstReal(1), cos_interval.getLower());
        
        // if contains singularities, return (-∞, ∞)
        auto result_lower = parser->mkIte(contains_zero, neg_inf, sec_lower);
        auto result_upper = parser->mkIte(contains_zero, pos_inf, sec_upper);
        
        // return the result interval
        return SMTInterval(parser, result_lower, result_upper,
                          parser->mkIte(contains_zero, parser->mkFalse(), cos_interval.isRightClosed()),
                          parser->mkIte(contains_zero, parser->mkFalse(), cos_interval.isLeftClosed()));
    }
    SMTInterval SMTInterval::csc() const{
        // calculate sine interval
        SMTInterval sin_interval = this->sin();
        auto ZERO = parser->mkConstReal(0);
        
        // check if sin interval contains 0 (cosecant has singularities at these points)
        auto contains_zero = parser->mkOr(
            parser->mkEq(sin_interval.getLower(), ZERO),
            parser->mkEq(sin_interval.getUpper(), ZERO),
            parser->mkAnd(parser->mkLt(sin_interval.getLower(), ZERO), 
                         parser->mkGt(sin_interval.getUpper(), ZERO))
        );
        
        // if contains 0, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // calculate csc values (csc(x) = 1/sin(x))
        auto csc_lower = parser->mkDiv(parser->mkConstReal(1), sin_interval.getUpper());
        auto csc_upper = parser->mkDiv(parser->mkConstReal(1), sin_interval.getLower());
        
        // if contains singularities, return (-∞, ∞)
        auto result_lower = parser->mkIte(contains_zero, neg_inf, csc_lower);
        auto result_upper = parser->mkIte(contains_zero, pos_inf, csc_upper);
        
        // return the result interval
        return SMTInterval(parser, result_lower, result_upper,
                          parser->mkIte(contains_zero, parser->mkFalse(), sin_interval.isRightClosed()),
                          parser->mkIte(contains_zero, parser->mkFalse(), sin_interval.isLeftClosed()));
    }
    SMTInterval SMTInterval::asin() const{
        // check if the interval is within the domain [-1, 1]

        // auto in_domain = parser->mkAnd(
        //     parser->mkGe(lower, parser->mkConstReal(-1)),
        //     parser->mkLe(upper, parser->mkConstReal(1))
        // );
        
        // // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for asin must be in range [-1, 1]");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // calculate asin values
        auto asin_lower = parser->mkAsin(lower);
        auto asin_upper = parser->mkAsin(upper);
        
        // return result interval
        return SMTInterval(parser, asin_lower, asin_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::acos() const{
        // check if the interval is within the domain [-1, 1]

        // auto in_domain = parser->mkAnd(
        //     parser->mkGe(lower, parser->mkConstReal(-1)),
        //     parser->mkLe(upper, parser->mkConstReal(1))
        // );
        
        // // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for acos must be in range [-1, 1]");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // calculate acos values (acos is monotonically decreasing)
        auto acos_lower = parser->mkAcos(upper);
        auto acos_upper = parser->mkAcos(lower);
        
        // return result interval (note the swapped closed flags)
        return SMTInterval(parser, acos_lower, acos_upper, rightClosed, leftClosed);
    }
    SMTInterval SMTInterval::atan() const{
        // atan函数单调递增，定义域是整个实数集
        auto atan_lower = parser->mkAtan(lower);
        auto atan_upper = parser->mkAtan(upper);
        
        // 返回结果区间
        return SMTInterval(parser, atan_lower, atan_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::acot() const{
        // acot(x) = π/2 - atan(x), acot is monotonically decreasing
        auto pi_half = parser->mkDivReal(parser->mkPi(), parser->mkConstReal(2));
        auto acot_lower = parser->mkSub(pi_half, parser->mkAtan(upper));
        auto acot_upper = parser->mkSub(pi_half, parser->mkAtan(lower));
        
        // return result interval (note the swapped closed flags)
        return SMTInterval(parser, acot_lower, acot_upper, rightClosed, leftClosed);
    }
    SMTInterval SMTInterval::asec() const{
        // asec domain is (-∞, -1] ∪ [1, ∞)
        auto neg_one = parser->mkConstReal(-1);
        auto one = parser->mkConstReal(1);
        // auto in_domain = parser->mkOr(
        //     parser->mkLe(upper, neg_one),
        //     parser->mkGe(lower, one)
        // );
        
        // // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for asec must be outside range (-1, 1)");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // handle special case: interval crosses -1 or 1
        auto crosses_boundary = parser->mkAnd(
            parser->mkLe(lower, neg_one),
            parser->mkGe(upper, one)
        );
        
        // if crossing boundary, return [0, π]
        auto zero = parser->mkConstReal(0);
        auto pi = parser->mkPi();
        
        // interval on negative half-axis
        auto on_negative = parser->mkLe(upper, neg_one);
        
        // calculate asec values
        auto asec_lower_neg = parser->mkAsec(upper);
        auto asec_upper_neg = parser->mkAsec(lower);
        
        auto asec_lower_pos = parser->mkAsec(lower);
        auto asec_upper_pos = parser->mkAsec(upper);
        
        // select correct values based on interval position
        auto asec_lower = parser->mkIte(crosses_boundary, zero,
                                       parser->mkIte(on_negative, asec_lower_neg, asec_lower_pos));
        auto asec_upper = parser->mkIte(crosses_boundary, pi,
                                       parser->mkIte(on_negative, asec_upper_neg, asec_upper_pos));
        
        // closed interval flags
        auto result_left_closed = parser->mkIte(crosses_boundary, parser->mkTrue(),
                                              parser->mkIte(on_negative, rightClosed, leftClosed));
        auto result_right_closed = parser->mkIte(crosses_boundary, parser->mkTrue(),
                                               parser->mkIte(on_negative, leftClosed, rightClosed));
        
        // return result interval
        return SMTInterval(parser, asec_lower, asec_upper, result_left_closed, result_right_closed);
    }
    SMTInterval SMTInterval::acsc() const{
        // acsc domain is (-∞, -1] ∪ [1, ∞)
        auto neg_one = parser->mkConstReal(-1);
        auto one = parser->mkConstReal(1);
        // auto in_domain = parser->mkOr(
        //     parser->mkLe(upper, neg_one),
        //     parser->mkGe(lower, one)
        // );
        
        // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for acsc must be outside range (-1, 1)");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // handle special case: interval crosses -1 or 1
        auto crosses_boundary = parser->mkAnd(
            parser->mkLe(lower, neg_one),
            parser->mkGe(upper, one)
        );
        
        // if crossing boundary, return [-π/2, π/2]
        auto neg_pi_half = parser->mkNeg(parser->mkDivReal(parser->mkPi(), parser->mkConstReal(2)));
        auto pi_half = parser->mkDivReal(parser->mkPi(), parser->mkConstReal(2));
        
        // interval on negative half-axis
        auto on_negative = parser->mkLe(upper, neg_one);
        
        // calculate acsc values
        auto acsc_lower_neg = parser->mkAcsc(upper);
        auto acsc_upper_neg = parser->mkAcsc(lower);
        
        auto acsc_lower_pos = parser->mkAcsc(lower);
        auto acsc_upper_pos = parser->mkAcsc(upper);
        
        // select correct values based on interval position
        auto acsc_lower = parser->mkIte(crosses_boundary, neg_pi_half,
                                       parser->mkIte(on_negative, acsc_lower_neg, acsc_lower_pos));
        auto acsc_upper = parser->mkIte(crosses_boundary, pi_half,
                                       parser->mkIte(on_negative, acsc_upper_neg, acsc_upper_pos));
        
        // closed interval flags
        auto result_left_closed = parser->mkIte(crosses_boundary, parser->mkTrue(),
                                              parser->mkIte(on_negative, rightClosed, leftClosed));
        auto result_right_closed = parser->mkIte(crosses_boundary, parser->mkTrue(),
                                               parser->mkIte(on_negative, leftClosed, rightClosed));
        
        // return result interval
        return SMTInterval(parser, acsc_lower, acsc_upper, result_left_closed, result_right_closed);
    }
    SMTInterval SMTInterval::sinh() const{
        // sinh is monotonically increasing
        auto sinh_lower = parser->mkSinh(lower);
        auto sinh_upper = parser->mkSinh(upper);
        
        // return result interval
        return SMTInterval(parser, sinh_lower, sinh_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::cosh() const{
        // cosh has minimum value 1 at x=0 and is symmetric
        auto ZERO = parser->mkConstReal(0);
        auto ONE = parser->mkConstReal(1);
        
        // check if interval contains 0
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // interval is on negative half-axis
        auto on_negative = parser->mkLt(upper, ZERO);
        
        // absolute values
        auto abs_lower = parser->mkAbs(lower);
        auto abs_upper = parser->mkAbs(upper);
        
        // calculate maximum absolute value
        auto max_abs = parser->mkMax({abs_lower, abs_upper});
        
        // calculate cosh values
        auto cosh_min = ONE;
        auto cosh_max = parser->mkCosh(max_abs);
        
        // if interval is completely on negative half-axis, swap bounds
        auto cosh_lower = parser->mkIte(on_negative, parser->mkCosh(upper), cosh_min);
        auto cosh_upper = parser->mkIte(on_negative, parser->mkCosh(lower), 
                                       parser->mkIte(contains_zero, cosh_max, parser->mkCosh(upper)));
        
        // closed interval flags
        auto result_left_closed = parser->mkIte(contains_zero, parser->mkTrue(), 
                                              parser->mkIte(on_negative, rightClosed, leftClosed));
        auto result_right_closed = parser->mkIte(on_negative, leftClosed, rightClosed);
        
        // return result interval
        return SMTInterval(parser, cosh_lower, cosh_upper, result_left_closed, result_right_closed);
    }
    SMTInterval SMTInterval::tanh() const{
        // tanh is monotonically increasing with range (-1, 1)
        auto tanh_lower = parser->mkTanh(lower);
        auto tanh_upper = parser->mkTanh(upper);
        
        // return result interval
        return SMTInterval(parser, tanh_lower, tanh_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::coth() const{
        // check if interval contains 0 (hyperbolic cotangent has singularity at 0)
        auto ZERO = parser->mkConstReal(0);
        auto ONE = parser->mkConstReal(1);
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // if contains 0, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // calculate coth values (coth(x) = 1/tanh(x))
        auto coth_lower = parser->mkDiv(ONE, parser->mkTanh(upper));
        auto coth_upper = parser->mkDiv(ONE, parser->mkTanh(lower));
        
        // if contains singularities, return (-∞, ∞)
        auto result_lower = parser->mkIte(contains_zero, neg_inf, coth_lower);
        auto result_upper = parser->mkIte(contains_zero, pos_inf, coth_upper);
        
        // return result interval
        return SMTInterval(parser, result_lower, result_upper,
                          parser->mkIte(contains_zero, parser->mkFalse(), rightClosed),
                          parser->mkIte(contains_zero, parser->mkFalse(), leftClosed));
    }
    SMTInterval SMTInterval::sech() const{
        // calculate cosh interval
        SMTInterval cosh_interval = this->cosh();
        auto ONE = parser->mkConstReal(1);
        
        // sech has range (0, 1] with maximum value 1 at x=0
        auto sech_lower = parser->mkDiv(ONE, cosh_interval.getUpper());
        auto sech_upper = parser->mkDiv(ONE, cosh_interval.getLower());
        
        // return result interval (note the swapped closed flags)
        return SMTInterval(parser, sech_lower, sech_upper, 
                          cosh_interval.isRightClosed(), cosh_interval.isLeftClosed());
    }
    SMTInterval SMTInterval::csch() const{
        // check if interval contains 0 (hyperbolic cosecant has singularity at 0)
        auto ZERO = parser->mkConstReal(0);
        auto ONE = parser->mkConstReal(1);
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // if contains 0, return (-∞, ∞)
        auto neg_inf = parser->mkNegInfinity(REAL_SORT);
        auto pos_inf = parser->mkPosInfinity(REAL_SORT);
        
        // calculate csch values (csch(x) = 1/sinh(x))
        auto csch_lower = parser->mkDiv(ONE, parser->mkSinh(upper));
        auto csch_upper = parser->mkDiv(ONE, parser->mkSinh(lower));
        
        // if contains singularities, return (-∞, ∞)
        auto result_lower = parser->mkIte(contains_zero, neg_inf, csch_lower);
        auto result_upper = parser->mkIte(contains_zero, pos_inf, csch_upper);
        
        // return result interval
        return SMTInterval(parser, result_lower, result_upper,
                          parser->mkIte(contains_zero, parser->mkFalse(), rightClosed),
                          parser->mkIte(contains_zero, parser->mkFalse(), leftClosed));
    }
    SMTInterval SMTInterval::asinh() const{
        // asinh is monotonically increasing with domain on the entire real line
        auto asinh_lower = parser->mkAsinh(lower);
        auto asinh_upper = parser->mkAsinh(upper);
        
        // return result interval
        return SMTInterval(parser, asinh_lower, asinh_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::acosh() const{
        // acosh domain is [1, ∞)

        // auto ONE = parser->mkConstReal(1);
        // auto in_domain = parser->mkGe(lower, ONE);
        
        // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for acosh must be >= 1");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // calculate acosh values
        auto acosh_lower = parser->mkAcosh(lower);
        auto acosh_upper = parser->mkAcosh(upper);
        
        // return result interval
        return SMTInterval(parser, acosh_lower, acosh_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::atanh() const{
        // atanh domain is (-1, 1)

        // auto NEG_ONE = parser->mkConstReal(-1);
        // auto ONE = parser->mkConstReal(1);
        // auto in_domain = parser->mkAnd(
        //     parser->mkGt(lower, NEG_ONE),
        //     parser->mkLt(upper, ONE)
        // );
        
        // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for atanh must be in range (-1, 1)");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // calculate atanh values
        auto atanh_lower = parser->mkAtanh(lower);
        auto atanh_upper = parser->mkAtanh(upper);
        
        // return result interval
        return SMTInterval(parser, atanh_lower, atanh_upper, leftClosed, rightClosed);
    }
    SMTInterval SMTInterval::acoth() const{
        // acoth domain is (-∞, -1) ∪ (1, ∞)
        auto NEG_ONE = parser->mkConstReal(-1);
        auto ONE = parser->mkConstReal(1);
        auto ZERO = parser->mkConstReal(0);
        auto in_domain = parser->mkOr(
            parser->mkLt(upper, NEG_ONE),
            parser->mkGt(lower, ONE)
        );
        
        // // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for acoth must be outside range [-1, 1]");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // check if interval crosses 0
        // auto crosses_zero = parser->mkAnd(
        //     parser->mkLt(lower, ZERO),
        //     parser->mkGt(upper, ZERO)
        // );
        
        // // if crossing 0, throw error
        // auto error_msg2 = parser->mkStr("Interval crosses zero, acoth not defined");
        // parser->mkIte(parser->mkNot(crosses_zero), parser->mkTrue(), parser->mkError(error_msg2));
        
        // interval on negative half-axis
        auto on_negative = parser->mkLt(upper, NEG_ONE);
        
        // calculate acoth values
        auto acoth_lower_neg = parser->mkAcoth(upper);
        auto acoth_upper_neg = parser->mkAcoth(lower);
        
        auto acoth_lower_pos = parser->mkAcoth(lower);
        auto acoth_upper_pos = parser->mkAcoth(upper);
        
        // select correct values based on interval position
        auto acoth_lower = parser->mkIte(on_negative, acoth_lower_neg, acoth_lower_pos);
        auto acoth_upper = parser->mkIte(on_negative, acoth_upper_neg, acoth_upper_pos);
        
        // closed interval flags
        auto result_left_closed = parser->mkIte(on_negative, rightClosed, leftClosed);
        auto result_right_closed = parser->mkIte(on_negative, leftClosed, rightClosed);
        
        // return result interval
        return SMTInterval(parser, acoth_lower, acoth_upper, result_left_closed, result_right_closed);
    }
    SMTInterval SMTInterval::asech() const{
        // asech domain is (0, 1]
        auto ZERO = parser->mkConstReal(0);
        auto ONE = parser->mkConstReal(1);
        // auto in_domain = parser->mkAnd(
        //     parser->mkGt(lower, ZERO),
        //     parser->mkLe(upper, ONE)
        // );
        
        // if out of domain, throw error
        // auto error_msg = parser->mkStr("Argument for asech must be in range (0, 1]");
        // parser->mkIte(in_domain, parser->mkTrue(), parser->mkError(error_msg));
        
        // calculate asech values (asech is monotonically decreasing)
        auto asech_lower = parser->mkAsech(upper);
        auto asech_upper = parser->mkAsech(lower);
        
        // return result interval (note the swapped closed flags)
        return SMTInterval(parser, asech_lower, asech_upper, rightClosed, leftClosed);
    }
    SMTInterval SMTInterval::acsch() const{
        // acsch domain is (-∞, 0) ∪ (0, ∞)
        auto ZERO = parser->mkConstReal(0);
        auto in_domain = parser->mkNot(parser->mkEq(lower, ZERO));
        
        // check if interval contains 0
        // auto contains_zero = parser->mkAnd(
        //     parser->mkLe(lower, ZERO),
        //     parser->mkGe(upper, ZERO)
        // );
        
        // if contains 0, throw error
        // auto error_msg = parser->mkStr("Argument for acsch must not include 0");
        // parser->mkIte(parser->mkNot(contains_zero), parser->mkTrue(), parser->mkError(error_msg));
        
        // interval on negative half-axis
        auto on_negative = parser->mkLt(upper, ZERO);
        
        // calculate acsch values
        auto acsch_lower_neg = parser->mkAcsch(upper);
        auto acsch_upper_neg = parser->mkAcsch(lower);
        
        auto acsch_lower_pos = parser->mkAcsch(lower);
        auto acsch_upper_pos = parser->mkAcsch(upper);
        
        // select correct values based on interval position
        auto acsch_lower = parser->mkIte(on_negative, acsch_lower_neg, acsch_lower_pos);
        auto acsch_upper = parser->mkIte(on_negative, acsch_upper_neg, acsch_upper_pos);
        
        // closed interval flags
        auto result_left_closed = parser->mkIte(on_negative, rightClosed, leftClosed);
        auto result_right_closed = parser->mkIte(on_negative, leftClosed, rightClosed);
        
        // return result interval
        return SMTInterval(parser, acsch_lower, acsch_upper, result_left_closed, result_right_closed);
    }
    
    // comparison operators
    std::shared_ptr<DAGNode> SMTInterval::isEqualTo(const SMTInterval& other) const{
        // Two intervals are equal if their bounds are equal and their closed flags match
        return parser->mkAnd({
            parser->mkEq(lower, other.lower),
            parser->mkEq(upper, other.upper),
            parser->mkEq(leftClosed, other.leftClosed),
            parser->mkEq(rightClosed, other.rightClosed)
        });
    }
    
    std::shared_ptr<DAGNode> SMTInterval::isNotEqualTo(const SMTInterval& other) const{
        // Negation of equality
        return parser->mkNot(this->isEqualTo(other));
    }
    
    std::shared_ptr<DAGNode> SMTInterval::isLessThan(const SMTInterval& other) const{
        // An interval is strictly less than another if its upper bound is less than
        // the other's lower bound, or if they touch but at least one is open at the touch point
        auto bounds_separate = parser->mkLt(upper, other.lower);
        auto bounds_touch = parser->mkEq(upper, other.lower);
        auto open_at_touch = parser->mkOr(parser->mkNot(rightClosed), parser->mkNot(other.leftClosed));
        
        return parser->mkOr(
            bounds_separate,
            parser->mkAnd(bounds_touch, open_at_touch)
        );
    }
    
    std::shared_ptr<DAGNode> SMTInterval::isLessThanOrEqualTo(const SMTInterval& other) const{
        // An interval is less than or equal to another if its upper bound is less than
        // or equal to the other's lower bound
        auto upper_le_other_lower = parser->mkLe(upper, other.lower);
        auto bounds_touch = parser->mkEq(upper, other.lower);
        auto closed_at_touch = parser->mkAnd(rightClosed, other.leftClosed);
        
        return parser->mkOr(
            parser->mkLt(upper, other.lower),
            parser->mkAnd(bounds_touch, closed_at_touch)
        );
    }
    
    std::shared_ptr<DAGNode> SMTInterval::isGreaterThan(const SMTInterval& other) const{
        // An interval is strictly greater than another if its lower bound is greater than
        // the other's upper bound, or if they touch but at least one is open at the touch point
        auto bounds_separate = parser->mkGt(lower, other.upper);
        auto bounds_touch = parser->mkEq(lower, other.upper);
        auto open_at_touch = parser->mkOr(parser->mkNot(leftClosed), parser->mkNot(other.rightClosed));
        
        return parser->mkOr(
            bounds_separate,
            parser->mkAnd(bounds_touch, open_at_touch)
        );
    }
    
    std::shared_ptr<DAGNode> SMTInterval::isGreaterThanOrEqualTo(const SMTInterval& other) const{
        // An interval is greater than or equal to another if its lower bound is greater than
        // or equal to the other's upper bound
        auto lower_ge_other_upper = parser->mkGe(lower, other.upper);
        auto bounds_touch = parser->mkEq(lower, other.upper);
        auto closed_at_touch = parser->mkAnd(leftClosed, other.rightClosed);
        
        return parser->mkOr(
            parser->mkGt(lower, other.upper),
            parser->mkAnd(bounds_touch, closed_at_touch)
        );
    }

    // assignment operators
    SMTInterval& SMTInterval::operator+=(const Number& value){
        auto result = (*this) + value;
        lower = result.lower;
        upper = result.upper;
        leftClosed = result.leftClosed;
        rightClosed = result.rightClosed;
        return *this;
    }
    
    SMTInterval& SMTInterval::operator-=(const Number& value){
        auto result = (*this) - value;
        lower = result.lower;
        upper = result.upper;
        leftClosed = result.leftClosed;
        rightClosed = result.rightClosed;
        return *this;
    }
    
    SMTInterval& SMTInterval::operator*=(const Number& value){
        auto result = (*this) * value;
        lower = result.lower;
        upper = result.upper;
        leftClosed = result.leftClosed;
        rightClosed = result.rightClosed;
        return *this;
    }
    
    SMTInterval& SMTInterval::operator/=(const Number& value){
        auto result = (*this) / value;
        lower = result.lower;
        upper = result.upper;
        leftClosed = result.leftClosed;
        rightClosed = result.rightClosed;
        return *this;
    }

    // Named binary operations
    SMTInterval SMTInterval::add(const Number& value) const{
        return (*this) + value;
    }
    
    SMTInterval SMTInterval::add(const SMTInterval& other) const{
        return (*this) + other;
    }
    
    SMTInterval SMTInterval::sub(const Number& value) const{
        return (*this) - value;
    }
    
    SMTInterval SMTInterval::sub(const SMTInterval& other) const{
        return (*this) - other;
    }
    
    SMTInterval SMTInterval::mul(const Number& value) const{
        return (*this) * value;
    }
    
    SMTInterval SMTInterval::mul(const SMTInterval& other) const{
        return (*this) * other;
    }
    
    SMTInterval SMTInterval::divReal(const Number& value) const{
        return (*this) / value;
    }
    
    SMTInterval SMTInterval::divReal(const SMTInterval& other) const{
        return (*this) / other;
    }
    
    SMTInterval SMTInterval::divInt(const Number& value) const{
        // Integer division truncates toward zero
        auto value_node = parser->mkConstReal(value.toReal());
        // auto is_zero = parser->mkEq(value_node, parser->mkConstReal(0));
        
        // // Error if division by zero
        // auto error_msg = parser->mkStr("Division by zero");
        // parser->mkIte(parser->mkNot(is_zero), parser->mkTrue(), parser->mkError(error_msg));
        
        // For integer division, we need to consider the truncation
        // This makes the bounds computation more complex
        auto ZERO = parser->mkConstReal(0);
        
        // Check signs of interval bounds and divisor
        auto lower_neg = parser->mkLt(lower, ZERO);
        auto upper_neg = parser->mkLt(upper, ZERO);
        auto value_neg = parser->mkLt(value_node, ZERO);
        
        // Compute division results for bounds
        auto div_lower = parser->mkDivInt(lower, value_node);
        auto div_upper = parser->mkDivInt(upper, value_node);
        
        // If divisor is negative, swap the bounds
        auto new_lower = parser->mkIte(value_neg, div_upper, div_lower);
        auto new_upper = parser->mkIte(value_neg, div_lower, div_upper);
        
        // The closedness is preserved if the bound is exact after division
        // Otherwise, it becomes open if truncation occurs
        auto lower_exact = parser->mkEq(parser->mkMul(div_lower, value_node), lower);
        auto upper_exact = parser->mkEq(parser->mkMul(div_upper, value_node), upper);
        
        auto new_left_closed = parser->mkIte(value_neg, 
                                           parser->mkIte(upper_exact, rightClosed, parser->mkFalse()),
                                           parser->mkIte(lower_exact, leftClosed, parser->mkFalse()));
        
        auto new_right_closed = parser->mkIte(value_neg,
                                            parser->mkIte(lower_exact, leftClosed, parser->mkFalse()),
                                            parser->mkIte(upper_exact, rightClosed, parser->mkFalse()));
        
        return SMTInterval(parser, new_lower, new_upper, new_left_closed, new_right_closed);
    }
    
    SMTInterval SMTInterval::divInt(const SMTInterval& other) const{
        // Integer division with interval is complex
        // We can only provide a conservative approximation
        auto ZERO = parser->mkConstReal(0);
        // auto other_contains_zero = parser->mkAnd(
        //     parser->mkLe(other.lower, ZERO),
        //     parser->mkGe(other.upper, ZERO)
        // );
        
        // // Error if division by interval containing zero
        // auto error_msg = parser->mkStr("Integer division by interval containing zero");
        // parser->mkIte(parser->mkNot(other_contains_zero), parser->mkTrue(), parser->mkError(error_msg));
        
        // For simplicity, we'll use a conservative approximation
        // Find the min and max values that can result from integer division
        
        // Get absolute minimum and maximum of the divisor
        auto abs_other_lower = parser->mkAbs(other.lower);
        auto abs_other_upper = parser->mkAbs(other.upper);
        auto min_abs_divisor = parser->mkMin({abs_other_lower, abs_other_upper});
        
        // Get absolute minimum and maximum of the dividend
        auto abs_lower = parser->mkAbs(lower);
        auto abs_upper = parser->mkAbs(upper);
        auto max_abs_dividend = parser->mkMax({abs_lower, abs_upper});
        
        // The range of the result is approximately [-max_abs_dividend/min_abs_divisor, max_abs_dividend/min_abs_divisor]
        auto approx_bound = parser->mkDivReal(max_abs_dividend, min_abs_divisor);
        
        return SMTInterval(parser, parser->mkNeg(approx_bound), approx_bound, parser->mkFalse(), parser->mkFalse());
    }
    
    SMTInterval SMTInterval::mod(const Number& value) const{
        return (*this) % value;
    }
    
    SMTInterval SMTInterval::mod(const SMTInterval& other) const{
        return (*this) % other;
    }
    
    SMTInterval SMTInterval::pow(const Number& exp) const{
        auto exp_node = parser->mkConstReal(exp.toReal());
        auto ZERO = parser->mkConstReal(0);
        auto ONE = parser->mkConstReal(1);
        
        // For e^0 = 1
        auto is_zero_exp = parser->mkEq(exp_node, ZERO);
        
        // For e^1 = e
        auto is_one_exp = parser->mkEq(exp_node, ONE);
        
        // For integer exponents, we could do more cases
        // Check if exponent is integer
        auto is_int_exp = parser->mkIsInt(exp_node);
        
        // Check if base interval is positive
        // auto this_positive = parser->mkGt(lower, ZERO);
        
        // If e^0, return [1,1]
        auto result_zero_exp = SMTInterval(parser, ONE, ONE, parser->mkTrue(), parser->mkTrue());
        
        // If e^1, return the original interval
        auto result_one_exp = *this;
        
        // For integer exponents with positive base, compute directly
        auto pow_lower = parser->mkPow(lower, exp_node);
        auto pow_upper = parser->mkPow(upper, exp_node);
        
        // For even integer exponents > 0
        auto is_even_exp = parser->mkAnd(is_int_exp, parser->mkEq(parser->mkMod(exp_node, parser->mkConstReal(2)), ZERO));
        auto is_pos_exp = parser->mkGt(exp_node, ZERO);
        auto is_even_pos_exp = parser->mkAnd(is_even_exp, is_pos_exp);
        
        // For even positive exponents with interval containing 0
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // For even positive exponents with interval containing 0,
        // the result minimum is 0 at x=0
        auto even_pos_min = parser->mkIte(
            parser->mkAnd(is_even_pos_exp, contains_zero),
            ZERO,
            parser->mkMin({pow_lower, pow_upper})
        );
        
        // // Negative base with non-integer exponent is undefined
        // auto error_neg_base = parser->mkStr("Negative base with non-integer exponent is undefined");
        // parser->mkIte(
        //     parser->mkOr({this_positive, is_int_exp}),
        //     parser->mkTrue(),
        //     parser->mkError(error_neg_base)
        // );
        
        // Now combine all cases
        auto result_lower = parser->mkIte(
            is_zero_exp,
            ONE,
            parser->mkIte(
                is_one_exp,
                lower,
                even_pos_min
            )
        );
        
        auto result_upper = parser->mkIte(
            is_zero_exp,
            ONE,
            parser->mkIte(
                is_one_exp,
                upper,
                parser->mkMax({pow_lower, pow_upper})
            )
        );
        
        return SMTInterval(parser, result_lower, result_upper, leftClosed, rightClosed);
    }
    
    SMTInterval SMTInterval::pow(const SMTInterval& exp) const{
        return (*this) ^ exp;
    }
    
    SMTInterval SMTInterval::atan2(const Number& y) const{
        // atan2(y, x) = arctan(y/x) with quadrant adjustment
        auto y_node = parser->mkConstReal(y.toReal());
        auto ZERO = parser->mkConstReal(0);
        auto PI = parser->mkPi();
        auto NEG_PI = parser->mkNeg(PI);
        auto PI_HALF = parser->mkDivReal(PI, parser->mkConstReal(2));
        auto NEG_PI_HALF = parser->mkNeg(PI_HALF);
        
        // Check if interval contains 0
        auto contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        
        // // Error if x-interval contains 0 and y is 0
        // auto error_msg = parser->mkStr("atan2(0, 0) is undefined");
        // parser->mkIte(
        //     parser->mkOr(
        //         parser->mkNot(contains_zero),
        //         parser->mkNot(parser->mkEq(y_node, ZERO))
        //     ),
        //     parser->mkTrue(),
        //     parser->mkError(error_msg)
        // );
        
        // Result depends on the signs of y and x
        auto y_pos = parser->mkGt(y_node, ZERO);
        auto y_neg = parser->mkLt(y_node, ZERO);
        
        // If x is positive, atan2(y, x) = arctan(y/x)
        // If x is negative and y is positive, atan2(y, x) = arctan(y/x) + π
        // If x is negative and y is negative, atan2(y, x) = arctan(y/x) - π
        // If x is zero and y is positive, atan2(y, x) = π/2
        // If x is zero and y is negative, atan2(y, x) = -π/2
        
        // For simplicity, if the interval contains both positive and negative values,
        // we'll return a conservative approximation of [-π, π]
        
        auto result_lower = parser->mkIte(
            contains_zero,
            parser->mkIte(y_pos, ZERO, NEG_PI),
            parser->mkIte(
                parser->mkLt(lower, ZERO),
                parser->mkIte(y_pos, ZERO, NEG_PI),
                parser->mkIte(
                    y_pos,
                    parser->mkAtan(parser->mkDivReal(y_node, upper)),
                    parser->mkAtan(parser->mkDivReal(y_node, lower))
                )
            )
        );
        
        auto result_upper = parser->mkIte(
            contains_zero,
            parser->mkIte(y_pos, PI, ZERO),
            parser->mkIte(
                parser->mkLt(upper, ZERO),
                parser->mkIte(y_pos, PI, ZERO),
                parser->mkIte(
                    y_pos,
                    parser->mkAtan(parser->mkDivReal(y_node, lower)),
                    parser->mkAtan(parser->mkDivReal(y_node, upper))
                )
            )
        );
        
        return SMTInterval(parser, result_lower, result_upper, parser->mkTrue(), parser->mkTrue());
    }
    
    SMTInterval SMTInterval::atan2(const SMTInterval& y) const{
        // this function calculates arctan2(y,x), where x is the current interval, and y is the parameter interval
        // arctan2(y,x) returns the angle of the point (x,y), range is [-π, π]

        // define constants
        auto ZERO = parser->mkConstReal(0);
        auto PI = parser->mkPi();
        auto NEG_PI = parser->mkNeg(PI);
        auto PI_HALF = parser->mkDivReal(PI, parser->mkConstReal(2));
        auto NEG_PI_HALF = parser->mkNeg(PI_HALF);

        // check if x and y intervals contain 0
        auto x_contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        auto y_contains_zero = parser->mkAnd(
            parser->mkLe(y.lower, ZERO),
            parser->mkGe(y.upper, ZERO)
        );

        // check which quadrant the interval is in
        // first quadrant: x > 0, y > 0
        auto x_positive = parser->mkGt(lower, ZERO);
        auto y_positive = parser->mkGt(y.lower, ZERO);
        auto first_quadrant = parser->mkAnd(x_positive, y_positive);

        // second quadrant: x < 0, y > 0
        auto x_negative = parser->mkLt(upper, ZERO);
        auto second_quadrant = parser->mkAnd(x_negative, y_positive);

        // third quadrant: x < 0, y < 0
        auto y_negative = parser->mkLt(y.upper, ZERO);
        auto third_quadrant = parser->mkAnd(x_negative, y_negative);

        // fourth quadrant: x > 0, y < 0
        auto fourth_quadrant = parser->mkAnd(x_positive, y_negative);

        // when x contains 0, y does not contain 0, the result is ±π/2
        auto x_zero_y_positive = parser->mkAnd(x_contains_zero, y_positive);
        auto x_zero_y_negative = parser->mkAnd(x_contains_zero, y_negative);

        // when two intervals are in different quadrants, calculate the corresponding arctan2 range
        
        // first quadrant: arctan(y/x) range is [0, π/2)
        auto first_q_lower = parser->mkAtan(parser->mkDivReal(y.lower, upper));
        auto first_q_upper = parser->mkAtan(parser->mkDivReal(y.upper, lower));
        
        // second quadrant: arctan(y/x) range is (π/2, π]
        auto second_q_lower = parser->mkAdd(PI, parser->mkAtan(parser->mkDivReal(y.lower, upper)));
        auto second_q_upper = parser->mkAdd(PI, parser->mkAtan(parser->mkDivReal(y.upper, lower)));
        
        // third quadrant: arctan(y/x) range is [-π, -π/2)
        auto third_q_lower = parser->mkSub(NEG_PI, parser->mkAtan(parser->mkDivReal(y.upper, lower)));
        auto third_q_upper = parser->mkSub(NEG_PI, parser->mkAtan(parser->mkDivReal(y.lower, upper)));
        
        // fourth quadrant: arctan(y/x) range is (-π/2, 0)
        auto fourth_q_lower = parser->mkAtan(parser->mkDivReal(y.upper, upper));
        auto fourth_q_upper = parser->mkAtan(parser->mkDivReal(y.lower, lower));

        // combine all possible cases
        // if the interval spans multiple quadrants, take the minimum and maximum possible values
        auto spans_quadrants = parser->mkNot(parser->mkOr({
            first_quadrant, second_quadrant, third_quadrant, fourth_quadrant,
            x_zero_y_positive, x_zero_y_negative
        }));

        // if the interval spans multiple quadrants, return a conservative estimate [-π, π]
        auto spans_result_lower = NEG_PI;
        auto spans_result_upper = PI;

        // determine the final lower bound based on the interval position
        auto result_lower = parser->mkIte(spans_quadrants, spans_result_lower,
            parser->mkIte(first_quadrant, first_q_lower,
                parser->mkIte(second_quadrant, second_q_lower,
                    parser->mkIte(third_quadrant, third_q_lower,
                        parser->mkIte(fourth_quadrant, fourth_q_lower,
                            parser->mkIte(x_zero_y_positive, PI_HALF, NEG_PI_HALF)
                        )
                    )
                )
            )
        );

        // determine the final upper bound based on the interval position
        auto result_upper = parser->mkIte(spans_quadrants, spans_result_upper,
            parser->mkIte(first_quadrant, first_q_upper,
                parser->mkIte(second_quadrant, second_q_upper,
                    parser->mkIte(third_quadrant, third_q_upper,
                        parser->mkIte(fourth_quadrant, fourth_q_upper,
                            parser->mkIte(x_zero_y_positive, PI_HALF, NEG_PI_HALF)
                        )
                    )
                )
            )
        );

        // special case: if both intervals contain 0, the result is the whole range [-π, π]
        auto both_contain_zero = parser->mkAnd(x_contains_zero, y_contains_zero);
        result_lower = parser->mkIte(both_contain_zero, NEG_PI, result_lower);
        result_upper = parser->mkIte(both_contain_zero, PI, result_upper);

        // determine the closure of the result interval
        auto result_left_closed = parser->mkIte(both_contain_zero, parser->mkTrue(), 
            parser->mkOr({
                parser->mkAnd(first_quadrant, leftClosed, y.leftClosed),
                parser->mkAnd(second_quadrant, leftClosed, y.leftClosed),
                parser->mkAnd(third_quadrant, rightClosed, y.rightClosed),
                parser->mkAnd(fourth_quadrant, rightClosed, y.leftClosed)
            })
        );
        
        auto result_right_closed = parser->mkIte(both_contain_zero, parser->mkTrue(), 
            parser->mkOr({
                parser->mkAnd(first_quadrant, rightClosed, y.rightClosed),
                parser->mkAnd(second_quadrant, rightClosed, y.rightClosed),
                parser->mkAnd(third_quadrant, leftClosed, y.leftClosed),
                parser->mkAnd(fourth_quadrant, leftClosed, y.rightClosed)
            })
        );

        return SMTInterval(parser, result_lower, result_upper, result_left_closed, result_right_closed);
    }

    // binary operators with SMTInterval
    SMTInterval SMTInterval::operator+(const SMTInterval& other) const{
        // [a,b] + [c,d] = [a+c, b+d]
        return SMTInterval(parser, 
                          parser->mkAdd(lower, other.lower), 
                          parser->mkAdd(upper, other.upper), 
                          parser->mkAnd(leftClosed, other.leftClosed), 
                          parser->mkAnd(rightClosed, other.rightClosed));
    }
    
    SMTInterval SMTInterval::operator-(const SMTInterval& other) const{
        // [a,b] - [c,d] = [a-d, b-c]
        return SMTInterval(parser, 
                          parser->mkSub(lower, other.upper), 
                          parser->mkSub(upper, other.lower), 
                          parser->mkAnd(leftClosed, other.rightClosed), 
                          parser->mkAnd(rightClosed, other.leftClosed));
    }
    
    SMTInterval SMTInterval::operator*(const SMTInterval& other) const{
        // For multiplication, we need to consider all combinations 
        // of endpoints and their signs
        
        // Check if intervals contain zero
        auto ZERO = parser->mkConstReal(0);
        auto this_contains_zero = parser->mkAnd(
            parser->mkLe(lower, ZERO),
            parser->mkGe(upper, ZERO)
        );
        auto other_contains_zero = parser->mkAnd(
            parser->mkLe(other.lower, ZERO),
            parser->mkGe(other.upper, ZERO)
        );
        
        // Calculate all possible products
        auto ll = parser->mkMul(lower, other.lower);
        auto lu = parser->mkMul(lower, other.upper);
        auto ul = parser->mkMul(upper, other.lower);
        auto uu = parser->mkMul(upper, other.upper);
        
        // Find minimum and maximum values
        auto min_val = parser->mkMin({ll, lu, ul, uu});
        auto max_val = parser->mkMax({ll, lu, ul, uu});
        
        // If either interval contains zero, the result could include zero
        auto result_contains_zero = parser->mkOr(this_contains_zero, other_contains_zero);
        
        // If both lower bounds are negative and both upper bounds are positive,
        // or if both lower bounds are positive and both upper bounds are negative,
        // then the closure is the product of the closures
        auto both_neg_lower = parser->mkAnd(
            parser->mkLt(lower, ZERO),
            parser->mkLt(other.lower, ZERO)
        );
        auto both_pos_upper = parser->mkAnd(
            parser->mkGt(upper, ZERO),
            parser->mkGt(other.upper, ZERO)
        );
        auto both_pos_lower = parser->mkAnd(
            parser->mkGt(lower, ZERO),
            parser->mkGt(other.lower, ZERO)
        );
        auto both_neg_upper = parser->mkAnd(
            parser->mkLt(upper, ZERO),
            parser->mkLt(other.upper, ZERO)
        );
        
        auto simple_case = parser->mkOr(
            parser->mkAnd(both_neg_lower, both_pos_upper),
            parser->mkAnd(both_pos_lower, both_neg_upper)
        );
        
        auto new_left_closed = parser->mkIte(result_contains_zero,
                                          parser->mkTrue(),
                                          parser->mkIte(simple_case,
                                                     parser->mkAnd(leftClosed, other.leftClosed),
                                                     parser->mkOr({
                                                         parser->mkAnd(parser->mkEq(min_val, ll), parser->mkAnd(leftClosed, other.leftClosed)),
                                                         parser->mkAnd(parser->mkEq(min_val, lu), parser->mkAnd(leftClosed, other.rightClosed)),
                                                         parser->mkAnd(parser->mkEq(min_val, ul), parser->mkAnd(rightClosed, other.leftClosed)),
                                                         parser->mkAnd(parser->mkEq(min_val, uu), parser->mkAnd(rightClosed, other.rightClosed))
                                                     })
                                            )
        );
        
        auto new_right_closed = parser->mkIte(result_contains_zero,
                                           parser->mkTrue(),
                                           parser->mkIte(simple_case,
                                                      parser->mkAnd(rightClosed, other.rightClosed),
                                                      parser->mkOr({
                                                          parser->mkAnd(parser->mkEq(max_val, ll), parser->mkAnd(leftClosed, other.leftClosed)),
                                                          parser->mkAnd(parser->mkEq(max_val, lu), parser->mkAnd(leftClosed, other.rightClosed)),
                                                          parser->mkAnd(parser->mkEq(max_val, ul), parser->mkAnd(rightClosed, other.leftClosed)),
                                                          parser->mkAnd(parser->mkEq(max_val, uu), parser->mkAnd(rightClosed, other.rightClosed))
                                                      })));
        
        return SMTInterval(parser, min_val, max_val, new_left_closed, new_right_closed);
    }
    
    SMTInterval SMTInterval::operator/(const SMTInterval& other) const{
        // Check if divisor contains zero
        auto ZERO = parser->mkConstReal(0);
        // auto other_contains_zero = parser->mkAnd(
        //     parser->mkLe(other.lower, ZERO),
        //     parser->mkGe(other.upper, ZERO)
        // );
        
        // // Error if division by interval containing zero
        // auto error_msg = parser->mkStr("Division by interval containing zero");
        // parser->mkIte(parser->mkNot(other_contains_zero), parser->mkTrue(), parser->mkError(error_msg));
        
        // Reciprocal of the divisor
        auto other_reciprocal = SMTInterval(parser,
                                          parser->mkDivReal(parser->mkConstReal(1), other.upper),
                                          parser->mkDivReal(parser->mkConstReal(1), other.lower),
                                          other.rightClosed,
                                          other.leftClosed);
        
        // Division is multiplication by the reciprocal
        return this->operator*(other_reciprocal);
    }
    
    SMTInterval SMTInterval::operator%(const SMTInterval& other) const{
        // Check if divisor contains zero
        auto ZERO = parser->mkConstReal(0);
        // auto other_contains_zero = parser->mkAnd(
        //     parser->mkLe(other.lower, ZERO),
        //     parser->mkGe(other.upper, ZERO)
        // );
        
        // // Error if modulo by interval containing zero
        // auto error_msg = parser->mkStr("Modulo by interval containing zero");
        // parser->mkIte(parser->mkNot(other_contains_zero), parser->mkTrue(), parser->mkError(error_msg));
        
        // For modulo, the result interval must be in [0, max(|other.lower|, |other.upper|))
        auto abs_lower = parser->mkAbs(other.lower);
        auto abs_upper = parser->mkAbs(other.upper);
        auto max_abs = parser->mkMax({abs_lower, abs_upper});
        
        // We return a conservative interval [0, max_abs-ε]
        return SMTInterval(parser, ZERO, 
                          parser->mkSub(max_abs, parser->mkConstReal(0.000001)), 
                          parser->mkTrue(), parser->mkTrue());
    }
    
    SMTInterval SMTInterval::operator^(const SMTInterval& other) const{
        // This is an approximation for interval exponentiation
        // We use exp(other * log(this)) when both intervals are positive
        auto ZERO = parser->mkConstReal(0);
        
        // Check if base interval is positive
        // auto this_positive = parser->mkGt(lower, ZERO);
        
        // // Error if base interval is not strictly positive
        // auto error_msg = parser->mkStr("Base interval must be strictly positive for power operation");
        // parser->mkIte(this_positive, parser->mkTrue(), parser->mkError(error_msg));
        
        // For integer exponents, we could handle more cases, but for simplicity
        // we'll just use the logarithm method for all cases
        auto log_this = this->ln();
        auto product = log_this * other;
        return SMTInterval(parser, 
                          parser->mkExp(product.lower), 
                          parser->mkExp(product.upper),
                          product.leftClosed,
                          product.rightClosed);
    }

} // namespace SMTLIBParser
