/* -*- Source -*-
 *
 * ICP Evaluation - Implementation of evaluation methods
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>, Kunhang Lv <lvkh@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia, Kunhang Lv
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

#include "tactics/icp/icp.h"
#include <iostream>
#include <cmath>
#include <limits>
#include <cassert>

// 添加M_PI常数定义
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

namespace ICP {

// Interval expression evaluation
Interval ICPSolver::evaluateExpression(std::shared_ptr<SMTLIBParser::DAGNode> expr,
                                        const std::map<std::string, std::pair<double, double>>& var_bounds) {
    if (!expr) {
        return Interval(1.0, -1.0, true, true); // Always false
    }
    else if (expr->isCInt()) {
        // Integer constant
        return Interval(parser->toInt(expr).toDouble(), parser->toInt(expr).toDouble(), true, true);
    }
    else if (expr->isCReal()) {
        // Real constant
        return Interval(parser->toReal(expr).toDouble(), parser->toReal(expr).toDouble(), true, true);
    }
    else if (expr->isVar()) {
        if (!var_bounds.empty() && var_bounds.find(expr->getName()) != var_bounds.end()) {
            return Interval(var_bounds.at(expr->getName()).first, var_bounds.at(expr->getName()).second, true, true);
        }
        // Variable
        std::string var_name = expr->getName();
        auto it = variables.find(var_name);
        if (it != variables.end()) {
            return it->second.domain;
        }
        return Interval(-std::numeric_limits<double>::infinity(), 
                         std::numeric_limits<double>::infinity(),
                         false, false); // 默认使用开区间表示无限区间
    }
    else if (expr->isAdd()) {
        // Addition
        Interval result(0.0, 0.0, true, true);
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            Interval child = evaluateExpression(expr->getChild(i), var_bounds);
            // 检查子表达式是否无解
            if (child.isEmpty()) {
                return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
            }
            result = add(result, child);
        }
        return result;
    }
    else if (expr->isSub()) {
        // Subtraction
        if (expr->getChildrenSize() == 1) {
            // Unary subtraction (negation)
            Interval operand = evaluateExpression(expr->getChild(0), var_bounds);
            // 检查子表达式是否无解
            if (operand.isEmpty()) {
                return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
            }
            // 取反时，闭合性也会对调：[a,b] 变为 [-b,-a]
            return Interval(-operand.high, -operand.low, operand.rightClosed, operand.leftClosed);
        } else if (expr->getChildrenSize() >= 2) {
            // Binary or n-ary subtraction
            Interval result = evaluateExpression(expr->getChild(0), var_bounds);
            // 检查第一个子表达式是否无解
            if (result.isEmpty()) {
                return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
            }
            
            for (size_t i = 1; i < expr->getChildrenSize(); ++i) {
                Interval child = evaluateExpression(expr->getChild(i), var_bounds);
                // 检查其他子表达式是否无解
                if (child.isEmpty()) {
                    return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
                }
                result = subtract(result, child);
            }
            return result;
        }
        return Interval(0.0, 0.0, true, true);
    }
    else if (expr->isMul()) {
        // Multiplication
        Interval result(1.0, 1.0, true, true);
        for (size_t i = 0; i < expr->getChildrenSize(); ++i) {
            Interval child = evaluateExpression(expr->getChild(i), var_bounds);
            // 检查子表达式是否无解
            if (child.isEmpty()) {
                return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
            }
            result = multiply(result, child);
        }
        return result;
    }
    else if (expr->isDivReal()) {
        // Real division
        if (expr->getChildrenSize() == 2) {
            Interval num = evaluateExpression(expr->getChild(0), var_bounds);
            Interval den = evaluateExpression(expr->getChild(1), var_bounds);
            
            // 检查子表达式是否无解
            if (num.isEmpty() || den.isEmpty()) {
                return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
            }
            
            return divide(num, den);
        }
        return Interval(0.0, 0.0, true, true);
    }
    // Transcendental functions
    else if (expr->isSin()) {
        // Sine function
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Check for full period
        double period = 2.0 * M_PI;
        if (arg.width() >= period) {
            return Interval(-1.0, 1.0, true, true); // Full range of sine
        }
        
        // Normalize to [0, 2π)
        double low_norm = std::fmod(arg.low, period);
        if (low_norm < 0) low_norm += period;
        
        double high_norm = std::fmod(arg.high, period);
        if (high_norm < 0) high_norm += period;
        
        // If we cross a period boundary
        if (high_norm < low_norm) {
            high_norm += period;
        }
        
        // Calculate extrema points
        double sin_low = std::sin(low_norm);
        double sin_high = std::sin(high_norm);
        
        double min_val = std::min(sin_low, sin_high);
        double max_val = std::max(sin_low, sin_high);
        
        // Check if we cross π/2 or 3π/2 points (extrema of sine)
        double pi_half = M_PI / 2.0;
        double three_pi_half = 3.0 * M_PI / 2.0;
        
        // Check if interval contains π/2 (maximum of sine = 1)
        if ((low_norm <= pi_half && high_norm >= pi_half) || 
            (low_norm <= pi_half + 2 * M_PI && high_norm >= pi_half + 2 * M_PI)) {
            max_val = 1.0;
        }
        
        // Check if interval contains 3π/2 (minimum of sine = -1)
        if ((low_norm <= three_pi_half && high_norm >= three_pi_half) || 
            (low_norm <= three_pi_half + 2 * M_PI && high_norm >= three_pi_half + 2 * M_PI)) {
            min_val = -1.0;
        }
        
        // 使用std::nextafter确保安全边界
        
        min_val -= std::numeric_limits<double>::epsilon()*std::abs(min_val);
        max_val += std::numeric_limits<double>::epsilon()*std::abs(max_val);
        min_val = std::nextafter(min_val, -std::numeric_limits<double>::infinity());
        max_val = std::nextafter(max_val, std::numeric_limits<double>::infinity());
        
        bool leftClosed = false;
        bool rightClosed = false;

        if (min_val < -1.0) {
            leftClosed = true;
        }
        if (max_val > 1.0) {
            rightClosed = true;
        }
        // 确保不会超出 sin 函数的范围 [-1, 1]
        min_val = std::max(min_val, -1.0);
        max_val = std::min(max_val, 1.0);
        
        // 扩大区间后使用开区间表示
        return Interval(min_val, max_val, leftClosed, rightClosed);
    }
    else if (expr->isCos()) {
        // Cosine function
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Check for full period
        double period = 2.0 * M_PI;
        if (arg.width() >= period) {
            return Interval(-1.0, 1.0, true, true); // Full range of cosine
        }
        
        // Normalize to [0, 2π)
        double low_norm = std::fmod(arg.low, period);
        if (low_norm < 0) low_norm += period;
        
        double high_norm = std::fmod(arg.high, period);
        if (high_norm < 0) high_norm += period;
        
        // If we cross a period boundary
        if (high_norm < low_norm) {
            high_norm += period;
        }
        
        // Calculate extrema points
        double cos_low = std::cos(low_norm);
        double cos_high = std::cos(high_norm);
        
        double min_val = std::min(cos_low, cos_high);
        double max_val = std::max(cos_low, cos_high);
        
        // Check if we cross 0 or π points (extrema of cosine)
        double zero = 0.0;
        double pi = M_PI;
        
        // Check if interval contains 0 (maximum of cosine = 1)
        if ((low_norm <= zero && high_norm >= zero) || 
            (low_norm <= zero + 2 * M_PI && high_norm >= zero + 2 * M_PI)) {
            max_val = 1.0;
        }
        
        // Check if interval contains π (minimum of cosine = -1)
        if ((low_norm <= pi && high_norm >= pi) || 
            (low_norm <= pi + 2 * M_PI && high_norm >= pi + 2 * M_PI)) {
            min_val = -1.0;
        }
        
        // 使用std::nextafter确保安全边界
        min_val -= std::numeric_limits<double>::epsilon()*std::abs(min_val);
        max_val += std::numeric_limits<double>::epsilon()*std::abs(max_val);
        min_val = std::nextafter(min_val, -std::numeric_limits<double>::infinity());
        max_val = std::nextafter(max_val, std::numeric_limits<double>::infinity());

        bool leftClosed = false;
        bool rightClosed = false;

        if (min_val < -1.0) {
            leftClosed = true;
        }
        if (max_val > 1.0) {
            rightClosed = true;
        }
        
        // 确保不会超出 cos 函数的范围 [-1, 1]
        min_val = std::max(min_val, -1.0);
        max_val = std::min(max_val, 1.0);
        
        // 扩大区间后使用开区间表示
        return Interval(min_val, max_val, leftClosed, rightClosed);
    }
    else if (expr->isTan()) {
        // Tangent function
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Normalize to [-π/2, π/2)
        double pi_half = M_PI / 2.0;
        double period = M_PI;
        
        // Check if the interval contains any singularity points (odd multiples of π/2)
        double low_mod = std::fmod(arg.low, period);
        if (low_mod < -pi_half) low_mod += period;
        if (low_mod >= pi_half) low_mod -= period;
        
        double high_mod = std::fmod(arg.high, period);
        if (high_mod < -pi_half) high_mod += period;
        if (high_mod >= pi_half) high_mod -= period;
        
        // If the interval crosses a singularity
        if ((low_mod <= -pi_half && high_mod >= -pi_half) || 
            (low_mod <= pi_half && high_mod >= pi_half)) {
            // Return infinite interval (tangent is unbounded)
            // 正切在奇数倍的π/2处有不连续点，使用开区间表示无穷区间
            return Interval(-std::numeric_limits<double>::infinity(), 
                            std::numeric_limits<double>::infinity(),
                            false, false);
        }
        
        // Otherwise, calculate the tangent at the endpoints
        double tan_low = std::tan(arg.low);
        double tan_high = std::tan(arg.high);
        if (tan_low <= tan_high) {
            std::swap(tan_low, tan_high);
        }

        tan_low -= std::numeric_limits<double>::epsilon()*std::abs(tan_low);
        tan_high += std::numeric_limits<double>::epsilon()*std::abs(tan_high);
        tan_low = std::nextafter(tan_low, -std::numeric_limits<double>::infinity());
        tan_high = std::nextafter(tan_high, std::numeric_limits<double>::infinity());
        
        return Interval(tan_low, tan_high, false, false);
    }
    else if (expr->isExp()) {
        // Exponential function (e^x)
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        double low = std::exp(arg.low);
        double high = std::exp(arg.high);
        
        low -= std::numeric_limits<double>::epsilon()*std::abs(low);
        high += std::numeric_limits<double>::epsilon()*std::abs(high);
        // 指数函数可能导致较大误差，使用两次nextafter
        low = std::nextafter(low, -std::numeric_limits<double>::infinity());
        high = std::nextafter(high, std::numeric_limits<double>::infinity());
        
        // 扩大区间后使用开区间表示
        return Interval(low, high, false, false);
    }
    else if (expr->isLog() || expr->isLn()) {
        // Natural logarithm (ln)
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Logarithm is only defined for positive numbers
        if (arg.high <= 0.0) {
            // Return an empty interval (undefined)
            return Interval(1.0, -1.0, false, false);
        }
        
        double low;
        bool leftClosed;
        
        if (arg.low <= 0.0) {
            low = -std::numeric_limits<double>::infinity();
            leftClosed = false; // 开区间，因为对0取对数是无穷大
        } else {
            low = std::log(arg.low);
            low -= std::numeric_limits<double>::epsilon()*std::abs(low);
            low = std::nextafter(low, -std::numeric_limits<double>::infinity());
            // 对于扩大的区间边界，使用开区间
            leftClosed = false;
        }
        
        double high = std::log(arg.high);
        high += std::numeric_limits<double>::epsilon()*std::abs(high);
        high = std::nextafter(high, std::numeric_limits<double>::infinity());
        // 对于扩大的区间边界，使用开区间
        bool rightClosed = false;
        
            
        return Interval(low, high, leftClosed, rightClosed);
    }
    else if (expr->isSqrt()) {
        // Square root function
        assert(expr->getChildrenSize() == 1);
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
    
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Square root is only defined for non-negative numbers
        if (arg.high < 0.0) {
            // Return an empty interval (undefined)
            return Interval(1.0, -1.0, false, false);
        }
        
        double low;
        bool leftClosed;
        
        if (arg.low < 0.0) {
            low = 0.0;
            leftClosed = true; // 闭区间，因为sqrt(0) = 0是有意义的
        } else {
            low = std::sqrt(arg.low);
            low -= std::numeric_limits<double>::epsilon()*std::abs(low);
            low = std::nextafter(low, -std::numeric_limits<double>::infinity());
            // 确保不会小于0
            low = std::max(0.0, low);
            // 对于扩大的区间边界，使用开区间
            leftClosed = false;
        }
        
        double high = std::sqrt(arg.high);
        // 对于扩大的区间边界，使用开区间
        bool rightClosed = false;
        high += std::numeric_limits<double>::epsilon()*std::abs(high);
        high = std::nextafter(high, std::numeric_limits<double>::infinity());
            
        return Interval(low, high, leftClosed, rightClosed);
    }
    else if (expr->isSafeSqrt()) {
        // Safe square root function
        assert(expr->getChildrenSize() == 1);   
        Interval arg = evaluateExpression(expr->getChild(0), var_bounds);
        
        // 检查子表达式是否无解
        if (arg.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // 检查子表达式是否为非负数
        if (arg.high < 0.0) {
            return Interval(0.0, 0.0, true, true); // 返回0表示无解
        }
        
        double low;
        bool leftClosed;
        
        if (arg.low < 0.0) {
            low = 0.0;
            leftClosed = true; // 闭区间，因为sqrt(0) = 0是有意义的
        } else {
            low = std::sqrt(arg.low);
            low -= std::numeric_limits<double>::epsilon()*std::abs(low);
            low = std::nextafter(low, -std::numeric_limits<double>::infinity());
            // 确保不会小于0
            low = std::max(0.0, low);
            // 对于扩大的区间边界，使用开区间
            leftClosed = false;
        }
        
        double high = std::sqrt(arg.high);
        high += std::numeric_limits<double>::epsilon()*std::abs(high);
        high = std::nextafter(high, std::numeric_limits<double>::infinity());
        // 对于扩大的区间边界，使用开区间
        bool rightClosed = false;
        
        return Interval(low, high, leftClosed, rightClosed);
    }
    else if (expr->isPow()) {
        // Power function (x^y)
        assert(expr->getChildrenSize() == 2);
        Interval base = evaluateExpression(expr->getChild(0), var_bounds);
        Interval exponent = evaluateExpression(expr->getChild(1), var_bounds);
    
        // 检查子表达式是否无解
        if (base.isEmpty() || exponent.isEmpty()) {
            return Interval(1.0, -1.0, false, false); // 返回空区间表示无解
        }
        
        // Special case: constant integer exponent
        if (exponent.low == exponent.high && exponent.low == std::floor(exponent.low)) {
            int n = static_cast<int>(exponent.low);
            
            double low = 0.0, high = 0.0;
            bool leftClosed = false, rightClosed = false;
            
            if (n == 0) {
                // x^0 = 1 (assuming x != 0)
                return Interval(1.0, 1.0, true, true);
            } else if (n > 0) {
                if (n % 2 == 0) {
                    // Even power
                    if (base.low >= 0.0) {
                        // [0, inf) ^ even = [0, inf)
                        low = std::pow(base.low, n);
                        high = std::pow(base.high, n);
                        
                        // 添加精度保护
                        low -= std::numeric_limits<double>::epsilon() * std::abs(low);
                        high += std::numeric_limits<double>::epsilon() * std::abs(high);
                        low = std::nextafter(low, -std::numeric_limits<double>::infinity());
                        high = std::nextafter(high, std::numeric_limits<double>::infinity());
                        if (low < 0) {
                            leftClosed = true;
                            low = 0;
                        }
                        
                        return Interval(low, high, leftClosed, false);
                    } else if (base.high <= 0.0) {
                        // (-inf, 0] ^ even = [0, inf)
                        // 翻转闭合性，因为负数的偶数次方会改变区间方向
                        low = std::pow(base.high, n);
                        high = std::pow(base.low, n);
                        
                        // 添加精度保护
                        low -= std::numeric_limits<double>::epsilon() * std::abs(low);
                        high += std::numeric_limits<double>::epsilon() * std::abs(high);
                        low = std::nextafter(low, -std::numeric_limits<double>::infinity());
                        high = std::nextafter(high, std::numeric_limits<double>::infinity());
                        if (low < 0) {
                            leftClosed = true;
                            low = 0;
                        }
                        
                        return Interval(low, high, leftClosed, false);
                    } else {
                        // Interval crosses zero, minimum at x=0
                        double max_pow = std::max(std::pow(std::abs(base.low), n), std::pow(std::abs(base.high), n));
                        
                        // 添加精度保护
                        max_pow += std::numeric_limits<double>::epsilon() * std::abs(max_pow);
                        max_pow = std::nextafter(max_pow, std::numeric_limits<double>::infinity());
                        
                        // 当区间跨越0时，在0处函数值为0，且是闭区间
                        return Interval(0.0, max_pow, true, false);
                    }
                } else {
                    // Odd power - monotonically increasing
                    low = std::pow(base.low, n);
                    high = std::pow(base.high, n);
                    
                    // 添加精度保护
                    low -= std::numeric_limits<double>::epsilon() * std::abs(low);
                    high += std::numeric_limits<double>::epsilon() * std::abs(high);
                    low = std::nextafter(low, -std::numeric_limits<double>::infinity());
                    high = std::nextafter(high, std::numeric_limits<double>::infinity());
                    
                    return Interval(low, high, false, false);
                }
            } else { // n < 0
                // Negative power - need to handle division by zero
                if (base.low <= 0.0 && base.high >= 0.0) {
                    // Interval crosses zero - division by zero
                    return Interval(-std::numeric_limits<double>::infinity(), 
                                    std::numeric_limits<double>::infinity(),
                                    false, false); // 无穷区间使用开区间表示
                } else {
                    // Applying x^(-n) = 1/(x^n)
                    if (n % 2 == 0) {
                        // Even negative power
                        if (base.low >= 0.0 || base.high <= 0.0) {
                            // 正数或负数底数
                            // 对于负偶数幂，结果总是正数
                            // 当底数为正时，函数单调递减
                            if (base.low >= 0.0) {
                                low = std::pow(base.high, n);
                                high = std::pow(base.low, n);
                            } 
                            // 当底数为负时，函数在远离0的方向上值较小
                            else if (base.high <= 0.0) {
                                // 对于负数，比较绝对值
                                low = std::pow(std::abs(base.low), n);
                                high = std::pow(std::abs(base.high), n);
                            }
                            
                            // 添加精度保护
                            low -= std::numeric_limits<double>::epsilon() * std::abs(low);
                            high += std::numeric_limits<double>::epsilon() * std::abs(high);
                            low = std::nextafter(low, -std::numeric_limits<double>::infinity());
                            high = std::nextafter(high, std::numeric_limits<double>::infinity());
                            
                            return Interval(low, high, false, false);
                        }
                    } else {
                        // Odd negative power
                        // 奇数负幂时，函数在整个实数域上都是单调递减的
                        // 并且保留原始数的符号
                        low = std::pow(base.high, n);
                        high = std::pow(base.low, n);
                        
                        // 添加精度保护
                        low -= std::numeric_limits<double>::epsilon() * std::abs(low);
                        high += std::numeric_limits<double>::epsilon() * std::abs(high);
                        low = std::nextafter(low, -std::numeric_limits<double>::infinity());
                        high = std::nextafter(high, std::numeric_limits<double>::infinity());
                        
                        return Interval(low, high, false, false);
                    }
                }
            }
        }
        
        // General case (non-integer or variable exponent)
        // This is a simplified implementation and might not be accurate in all cases
        if (base.low > 0.0) {
            // Positive base - can use standard pow
            double vals[4] = {
                std::pow(base.low, exponent.low),
                std::pow(base.low, exponent.high),
                std::pow(base.high, exponent.low),
                std::pow(base.high, exponent.high)
            };
            
            double low = std::min({vals[0], vals[1], vals[2], vals[3]});
            double high = std::max({vals[0], vals[1], vals[2], vals[3]});
            
            // 添加精度保护
            low -= std::numeric_limits<double>::epsilon() * std::abs(low);
            high += std::numeric_limits<double>::epsilon() * std::abs(high);
            low = std::nextafter(low, -std::numeric_limits<double>::infinity());
            high = std::nextafter(high, std::numeric_limits<double>::infinity());
            
            return Interval(low, high, false, false);
        }
        
        // For other cases, implement a more sophisticated method
        // or return a wide interval that safely covers all possibilities
        return Interval(-std::numeric_limits<double>::infinity(), 
                        std::numeric_limits<double>::infinity(),
                        false, false); // 无穷区间使用开区间表示
    }
    
    // For unhandled operators, return an uncertain interval
    return Interval(-std::numeric_limits<double>::infinity(), 
                     std::numeric_limits<double>::infinity(),
                    false, false); // 无穷区间使用开区间表示
}

} // namespace ICP 
