/* -*- Header -*-
 *
 * The SMT SMTInterval Class
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

#ifndef _SMT_INTERVAL_H
#define _SMT_INTERVAL_H
#include "dag.h"
#include "parser.h"

namespace SMTLIBParser{

    class SMTInterval{
        private:
            std::shared_ptr<Parser> parser;
            std::shared_ptr<DAGNode> lower;
            std::shared_ptr<DAGNode> upper;
            bool leftClosed;
            bool rightClosed;
        public:
            SMTInterval(
                std::shared_ptr<Parser> parser,
                std::shared_ptr<DAGNode> lower, 
                std::shared_ptr<DAGNode> upper, 
                bool leftClosed, 
                bool rightClosed
            );
            SMTInterval(const SMTInterval& other);
            SMTInterval& operator=(const SMTInterval& other);
            ~SMTInterval();

            // setters
            // warning: these functions will change the SMTInterval
            void setLower(std::shared_ptr<DAGNode> lower);
            void setUpper(std::shared_ptr<DAGNode> upper);
            void setLeftClosed(bool leftClosed);
            void setRightClosed(bool rightClosed);

            // getters
            std::shared_ptr<DAGNode> getLower() const;
            std::shared_ptr<DAGNode> getUpper() const;
            bool isLeftClosed() const;
            bool isRightClosed() const;
            bool isLeftUnbounded() const;
            bool isRightUnbounded() const;
            std::shared_ptr<DAGNode> midpoint() const;
            std::string toString() const;
            void getIntegers(std::vector<std::shared_ptr<DAGNode>>& integers) const;
            bool isPoint() const;
            bool isEmpty() const;
            std::shared_ptr<DAGNode> width() const;
            bool contains(const std::shared_ptr<DAGNode>& value) const;
            bool isSubsetOf(const SMTInterval& other) const;
            bool isSubsetEqOf(const SMTInterval& other) const;
            bool isSupersetOf(const SMTInterval& other) const;
            bool isDisjointFrom(const SMTInterval& other) const;
            bool isIntersectingWith(const SMTInterval& other) const;
            SMTInterval intersection(const SMTInterval& other) const;
            SMTInterval unionWith(const SMTInterval& other) const;
            std::vector<SMTInterval> difference(const SMTInterval& other) const;
            size_t getIntervalIntCount() const;

            // unary operators
            SMTInterval operator++() const;
            SMTInterval operator--() const;
            SMTInterval operator-() const;
            SMTInterval operator+() const;
            SMTInterval operator~() const;
            SMTInterval operator!() const;
            SMTInterval operator++(int) const;
            SMTInterval operator--(int) const;
            SMTInterval negate() const;
            SMTInterval abs() const;
            SMTInterval lb() const;
            SMTInterval ln() const;
            SMTInterval lg() const;
            SMTInterval exp() const;
            SMTInterval sqrt() const;
            SMTInterval safesqrt() const;
            SMTInterval sin() const;
            SMTInterval cos() const;
            SMTInterval tan() const;
            SMTInterval cot() const;
            SMTInterval sec() const;
            SMTInterval csc() const;
            SMTInterval asin() const;
            SMTInterval acos() const;
            SMTInterval atan() const;
            SMTInterval acot() const;
            SMTInterval asec() const;
            SMTInterval acsc() const;
            SMTInterval sinh() const;
            SMTInterval cosh() const;
            SMTInterval tanh() const;
            SMTInterval coth() const;
            SMTInterval sech() const;
            SMTInterval csch() const;
            SMTInterval asinh() const;
            SMTInterval acosh() const;
            SMTInterval atanh() const;
            SMTInterval acoth() const;
            SMTInterval asech() const;
            SMTInterval acsch() const;
            
            // binary operators
            SMTInterval operator+(const Number& value) const;
            SMTInterval operator-(const Number& value) const;
            SMTInterval operator*(const Number& value) const;
            SMTInterval operator/(const Number& value) const;
            SMTInterval operator%(const Number& value) const;
            SMTInterval operator^(const Number& value) const;
            SMTInterval operator+(const SMTInterval& other) const;
            SMTInterval operator-(const SMTInterval& other) const;
            SMTInterval operator*(const SMTInterval& other) const;
            SMTInterval operator/(const SMTInterval& other) const;
            SMTInterval operator%(const SMTInterval& other) const;
            SMTInterval operator^(const SMTInterval& other) const;
            SMTInterval add(const Number& value) const;
            SMTInterval add(const SMTInterval& other) const;
            SMTInterval sub(const Number& value) const;
            SMTInterval sub(const SMTInterval& other) const;
            SMTInterval mul(const Number& value) const;
            SMTInterval mul(const SMTInterval& other) const;
            SMTInterval divReal(const Number& value) const;
            SMTInterval divReal(const SMTInterval& other) const;
            SMTInterval divInt(const Number& value) const;
            SMTInterval divInt(const SMTInterval& other) const;
            SMTInterval mod(const Number& value) const;
            SMTInterval mod(const SMTInterval& other) const;
            SMTInterval pow(const Number& exp) const;
            SMTInterval pow(const SMTInterval& exp) const;
            SMTInterval atan2(const Number& x) const;
            SMTInterval atan2(const SMTInterval& x) const;
            

            // comparison operators
            bool operator==(const SMTInterval& other) const;
            bool operator!=(const SMTInterval& other) const;
            bool operator<(const SMTInterval& other) const;
            bool operator<=(const SMTInterval& other) const;
            bool operator>(const SMTInterval& other) const;
            bool operator>=(const SMTInterval& other) const;

            // assignment operators
            SMTInterval& operator+=(const Number& value);
            SMTInterval& operator-=(const Number& value);
            SMTInterval& operator*=(const Number& value);
            SMTInterval& operator/=(const Number& value);

            // 静态方法，用于处理多个区间
            static std::vector<SMTInterval> unionMulti(const std::vector<SMTInterval>& intervals);
    };
}

#endif