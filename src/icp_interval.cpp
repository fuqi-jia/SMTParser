/* -*- Source -*-
 *
 * ICP Interval - Implementation of interval operations
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


// 区间交集操作
Interval ICPSolver::intersect(const Interval& a, const Interval& b) {
    double low = std::max(a.low, b.low);
    double high = std::min(a.high, b.high);
    
    // 处理边界点的闭合性
    bool leftClosed = (a.low < b.low) ? b.leftClosed : 
                      (a.low > b.low) ? a.leftClosed :
                      (a.leftClosed && b.leftClosed);
    
    bool rightClosed = (a.high > b.high) ? b.rightClosed : 
                       (a.high < b.high) ? a.rightClosed :
                       (a.rightClosed && b.rightClosed);
    
    return Interval(low, high, leftClosed, rightClosed);
}

// 区间并集操作
std::vector<Interval> ICPSolver::union_(const Interval& a, const Interval& b) {
    // 检查区间是否为空
    if (a.isEmpty()) return {b};
    if (b.isEmpty()) return {a};
    
    // 检查区间是否相交或相邻
    bool intersectOrAdjacent = !(a.high < b.low || (a.high == b.low && !a.rightClosed && !b.leftClosed) ||
                               b.high < a.low || (b.high == a.low && !b.rightClosed && !a.leftClosed));
    
    if (intersectOrAdjacent) {
        // 区间相交或相邻，可以合并为一个区间
        double low = std::min(a.low, b.low);
        double high = std::max(a.high, b.high);
        
        // 确定边界闭合性
        bool leftClosed = (a.low < b.low) ? a.leftClosed : 
                          (b.low < a.low) ? b.leftClosed :
                          (a.leftClosed || b.leftClosed); // 如果下界相等，取两者中的闭区间
        
        bool rightClosed = (a.high > b.high) ? a.rightClosed : 
                           (b.high > a.high) ? b.rightClosed :
                           (a.rightClosed || b.rightClosed); // 如果上界相等，取两者中的闭区间
        
        return {Interval(low, high, leftClosed, rightClosed)};
    } else {
        // 区间不相交且不相邻，返回两个独立区间
        // 按照区间下界排序
        if (a.low <= b.low) {
            return {a, b};
        } else {
            return {b, a};
        }
    }
}

// 多个区间的并集操作
std::vector<Interval> ICPSolver::union_(const std::vector<Interval>& intervals) {
    if (intervals.empty()) return {};
    if (intervals.size() == 1) return {intervals[0]};
    
    // 对区间按下界排序
    std::vector<Interval> sortedIntervals = intervals;
    std::sort(sortedIntervals.begin(), sortedIntervals.end(), 
              [](const Interval& a, const Interval& b) { 
                  return a.low < b.low || (a.low == b.low && a.leftClosed > b.leftClosed); 
              });
    
    std::vector<Interval> result;
    Interval current = sortedIntervals[0];
    
    for (size_t i = 1; i < sortedIntervals.size(); ++i) {
        // 获取当前区间与下一个区间的并集
        std::vector<Interval> unionResult = union_(current, sortedIntervals[i]);
        
        if (unionResult.size() == 1) {
            // 如果合并成一个区间，更新当前区间
            current = unionResult[0];
        } else {
            // 如果是两个不相交区间，将第一个区间加入结果，更新当前区间为第二个
            result.push_back(unionResult[0]);
            current = unionResult[1];
        }
    }
    
    // 添加最后一个区间
    result.push_back(current);
    
    return result;
}

// 区间是否是b的真子集
bool ICPSolver::isSubSetOf(const Interval& a, const Interval& b) {
    // 真子集要求A严格包含于B，即A必须是B的子集且A≠B
    // A是B的子集
    bool isSubset = (b.low <= a.low && b.high >= a.high && 
                   (b.leftClosed || a.low > b.low || !a.leftClosed) && 
                   (b.rightClosed || a.high < b.high || !a.rightClosed));
    
    // A与B不相等 - 至少有一个边界不同
    bool notEqual = (a.low > b.low || a.high < b.high ||
                    (a.low == b.low && a.leftClosed != b.leftClosed) ||
                    (a.high == b.high && a.rightClosed != b.rightClosed));
    
    return isSubset && notEqual;
}

// 区间是否是b的子集
bool ICPSolver::isSubSetEqOf(const Interval& a, const Interval& b) {
    // 子集要求A中的所有元素都在B中
    return (b.low <= a.low && b.high >= a.high && 
           (b.leftClosed || a.low > b.low || !a.leftClosed) && 
           (b.rightClosed || a.high < b.high || !a.rightClosed));
}

// 区间是否不相交
bool ICPSolver::isDisjoint(const Interval& a, const Interval& b) {
    return a.high < b.low || (a.high == b.low && (!a.rightClosed || !b.leftClosed)) ||
           a.low > b.high || (a.low == b.high && (!a.leftClosed || !b.rightClosed));
}

// 区间是否包含某个值
bool ICPSolver::contains(const Interval& a, const double value) {
    return a.low <= value && a.high >= value &&
           (a.leftClosed || a.low < value || !a.leftClosed) &&
           (a.rightClosed || a.high > value || !a.rightClosed);
}

// 区间中包含的整数
size_t ICPSolver::getIntervalIntCount(const Interval& a) {
    if (a.isEmpty()) return 0;
    if (a.isPoint()) return 1;
    if (a.leftClosed && a.rightClosed) {
        return static_cast<size_t>(std::ceil(a.high) - std::floor(a.low) + 1);
    }
    else if (a.leftClosed && !a.rightClosed) {
        return static_cast<size_t>(std::ceil(a.high) - std::floor(a.low));
    }
    else if (!a.leftClosed && a.rightClosed) {
        return static_cast<size_t>(std::ceil(a.high) - std::floor(a.low));
    }
    else{
        // 开区间
        return static_cast<size_t>(std::ceil(a.high) - std::floor(a.low) - 1);
    }
}

// 区间差集操作 A - B
std::vector<Interval> ICPSolver::difference(const Interval& a, const Interval& b) {
    // 如果区间不相交，返回A
    if (a.high < b.low || (a.high == b.low && (!a.rightClosed || !b.leftClosed)) ||
        a.low > b.high || (a.low == b.high && (!a.leftClosed || !b.rightClosed))) {
        return {a};
    }
    
    // 如果B完全包含A，返回空集
    if ((b.low < a.low || (b.low == a.low && b.leftClosed >= a.leftClosed)) &&
        (b.high > a.high || (b.high == a.high && b.rightClosed >= a.rightClosed))) {
        return {};
    }
    
    std::vector<Interval> result;
    
    // 如果B在A的内部，将A分割成两个区间
    if ((b.low > a.low || (b.low == a.low && !b.leftClosed && a.leftClosed)) &&
        (b.high < a.high || (b.high == a.high && !b.rightClosed && a.rightClosed))) {
        
        // 左侧区间: [a.low, b.low)
        bool rightClosed = !b.leftClosed;
        result.push_back(Interval(a.low, b.low, a.leftClosed, rightClosed));
        
        // 右侧区间: (b.high, a.high]
        bool leftClosed = !b.rightClosed;
        result.push_back(Interval(b.high, a.high, leftClosed, a.rightClosed));
        
        return result;
    }
    
    // 如果B从左侧覆盖A的一部分
    if ((b.low <= a.low || (b.low == a.low && b.leftClosed >= a.leftClosed)) &&
        (b.high < a.high || (b.high == a.high && !b.rightClosed && a.rightClosed))) {
        
        // 右侧剩余部分: (b.high, a.high]
        bool leftClosed = !b.rightClosed;
        result.push_back(Interval(b.high, a.high, leftClosed, a.rightClosed));
        
        return result;
    }
    
    // 如果B从右侧覆盖A的一部分
    if ((b.low > a.low || (b.low == a.low && !b.leftClosed && a.leftClosed)) &&
        (b.high >= a.high || (b.high == a.high && b.rightClosed >= a.rightClosed))) {
        
        // 左侧剩余部分: [a.low, b.low)
        bool rightClosed = !b.leftClosed;
        result.push_back(Interval(a.low, b.low, a.leftClosed, rightClosed));
        
        return result;
    }
    
    // 理论上不应该到达这里，但为安全起见返回空集
    return {};
}

// 区间加法操作
Interval ICPSolver::add(const Interval& a, const Interval& b) {
    // 区间加法保持端点的闭合性
    double low = a.low + b.low;
    double high = a.high + b.high;

    low -= std::numeric_limits<double>::epsilon()*std::abs(low);
    high += std::numeric_limits<double>::epsilon()*std::abs(high);
    
    // 使用std::nextafter获取下一个或上一个可表示的浮点数
    // 确保区间包含真实值
    low = std::nextafter(low, -std::numeric_limits<double>::infinity());
    high = std::nextafter(high, std::numeric_limits<double>::infinity());
    
    // 扩大区间后使用开区间表示，因为真实值不太可能落在新边界上
    return Interval(low, high, false, false);
}

// 区间减法操作
Interval ICPSolver::subtract(const Interval& a, const Interval& b) {
    // 区间减法: a - b = a + (-b)
    // (-b) = [-b.high, -b.low] 且闭合性与b相反
    double low = a.low - b.high;
    double high = a.high - b.low;

    low -= std::numeric_limits<double>::epsilon()*std::abs(low);
    high += std::numeric_limits<double>::epsilon()*std::abs(high);
    
    // 使用std::nextafter获取下一个或上一个可表示的浮点数
    // 确保区间包含真实值
    low = std::nextafter(low, -std::numeric_limits<double>::infinity());
    high = std::nextafter(high, std::numeric_limits<double>::infinity());
    
    // 扩大区间后使用开区间表示
    return Interval(low, high, false, false);
}

// 区间乘法操作
Interval ICPSolver::multiply(const Interval& a, const Interval& b) {
    double p1 = a.low * b.low;
    double p2 = a.low * b.high;
    double p3 = a.high * b.low;
    double p4 = a.high * b.high;
    
    double low = std::min({p1, p2, p3, p4});
    double high = std::max({p1, p2, p3, p4});
    
    // 乘法可能导致更大的误差，使用两次nextafter
    
    low -= std::numeric_limits<double>::epsilon()*std::abs(low);
    high += std::numeric_limits<double>::epsilon()*std::abs(high);
    
    low = std::nextafter(low, -std::numeric_limits<double>::infinity());
    high = std::nextafter(high, std::numeric_limits<double>::infinity());
    
    // 扩大区间后使用开区间表示
    return Interval(low, high, false, false);
}

// 区间除法操作
Interval ICPSolver::divide(const Interval& a, const Interval& b) {
    // 如果除数区间包含0，结果不确定
    if ((b.low < 0 && b.high > 0) || 
        (b.low == 0 && b.leftClosed) || 
        (b.high == 0 && b.rightClosed)) {
        // 返回无穷区间表示不确定性
        return Interval(-std::numeric_limits<double>::infinity(), 
                         std::numeric_limits<double>::infinity(), 
                         false, false); // 使用开区间表示
    }
    
    double p1 = a.low / b.low;
    double p2 = a.low / b.high;
    double p3 = a.high / b.low;
    double p4 = a.high / b.high;
    
    double low = std::min({p1, p2, p3, p4});
    double high = std::max({p1, p2, p3, p4});
    
    
    low -= std::numeric_limits<double>::epsilon()*std::abs(low);
    high += std::numeric_limits<double>::epsilon()*std::abs(high);
    
    low = std::nextafter(low, -std::numeric_limits<double>::infinity());
    high = std::nextafter(high, std::numeric_limits<double>::infinity());
    
    // 扩大区间后使用开区间表示
    return Interval(low, high, false, false);
}

// 实现区间约束
bool ICPSolver::enforceConstraint(const std::string& var_name, const Interval& constraint) {
    auto it = variables.find(var_name);
    if (it == variables.end()) {
        return false;
    }
    
    Interval& domain = it->second.domain;
    Interval new_domain = intersect(domain, constraint);
    
    // 如果是整数变量，调整区间边界为整数
    if (it->second.isInteger) {
        // 对于左端点，如果它是开区间，向上取整；如果是闭区间，向上取整
        if (!new_domain.leftClosed) {
            new_domain.low = std::ceil(new_domain.low);
            new_domain.leftClosed = true;  // 转为闭区间，因为整数点是离散的
        } else {
            new_domain.low = std::ceil(new_domain.low - 1e-10);  // 防止浮点误差
        }
        
        // 对于右端点，如果它是开区间，向下取整；如果是闭区间，向下取整
        if (!new_domain.rightClosed) {
            new_domain.high = std::floor(new_domain.high);
            new_domain.rightClosed = true;  // 转为闭区间，因为整数点是离散的
        } else {
            new_domain.high = std::floor(new_domain.high + 1e-10);  // 防止浮点误差
        }
    }
    
    // 检查区间是否有变化
    bool changed = new_domain.low != domain.low || 
                   new_domain.high != domain.high ||
                   new_domain.leftClosed != domain.leftClosed ||
                   new_domain.rightClosed != domain.rightClosed;
    
    if (changed) {
        domain = new_domain;
        return true;
    }
    
    return false;
}

// Extract variables from DAG node
void ICPSolver::extractVariables(std::shared_ptr<SMTLIBParser::DAGNode> node) {
    if (!node) return;
    
    // If node is a variable
    if (node->isVar()) {
        std::string var_name = node->getName();
        
        // If variable has not been added yet
        if (variables.find(var_name) == variables.end()) {
            // Set initial domain based on variable type
            auto sort = node->getSort();
            
            // 处理布尔变量
            if (sort->isBool()) {
                // 布尔变量默认为未知状态
                if (config.verbose) {
                    std::cout << "Adding boolean variable: " << var_name << " (domain: unknown)" << std::endl;
                }
                variables[var_name] = VariableConstraint(var_name, BooleanDomain::UNKNOWN);
            } 
            else {
                // 对于数值变量（整数和实数）的处理
                bool isInt = sort->isInt();
                
                // 默认区间范围，对于全域搜索使用更大的范围
                double default_low = config.use_global_search ? -1e6 : -1000.0;
                double default_high = config.use_global_search ? 1e6 : 1000.0;
                bool leftClosed = true;
                bool rightClosed = true;
                
                // 对于全域搜索，使用真正的无穷区间（开区间）
                if (config.use_global_search) {
                    default_low = -std::numeric_limits<double>::infinity();
                    default_high = std::numeric_limits<double>::infinity();
                    leftClosed = false;  // 无穷区间使用开区间
                    rightClosed = false; // 无穷区间使用开区间
                }
                
                Interval domain(default_low, default_high, leftClosed, rightClosed);
                
                // only use random intervals when use_random_intervals is true
                if (use_random_intervals) {
                    // use randomly generated interval, not fixed value
                    double low, high;
                    if (isInt) {
                        // use smaller range for integer variables
                        std::uniform_int_distribution<int> dist(-100, 100);
                        int a = dist(gen);
                        int b = dist(gen);
                        low = std::min(a, b);
                        high = std::max(a, b);
                        // ensure the interval has at least one integer
                        if (high - low < 1.0) {
                            high = low + 1.0;
                        }
                    } else {
                        // use larger range for real variables
                        std::uniform_real_distribution<double> dist(-1000.0, 1000.0);
                        double a = dist(gen);
                        double b = dist(gen);
                        low = std::min(a, b);
                        high = std::max(a, b);
                        // ensure the interval is not too small
                        if (high - low < 0.1) {
                            high = low + 0.1;
                        }
                        
                        // 对于实数变量，随机决定是否使用开区间
                        std::uniform_int_distribution<int> bool_dist(0, 1);
                        bool leftClosed = bool_dist(gen) == 1;
                        bool rightClosed = bool_dist(gen) == 1;
                        domain = Interval(low, high, leftClosed, rightClosed);
                        
                        if (config.verbose) {
                            std::cout << "Using random interval for variable: " << var_name 
                                      << " " << (leftClosed ? "[" : "(") 
                                      << domain.low << ", " << domain.high 
                                      << (rightClosed ? "]" : ")") 
                                      << std::endl;
                        }
                        
                        variables[var_name] = VariableConstraint(var_name, domain, isInt);
                        
                        // 递归处理子节点
                        for (size_t i = 0; i < node->getChildrenSize(); ++i) {
                            extractVariables(node->getChild(i));
                        }
                        
                        return;  // 提前返回，避免重复添加变量
                    }
                    
                    domain = Interval(low, high, true, true); // 整数变量使用闭区间
                    if (config.verbose) {
                        std::cout << "Using random interval for variable: " << var_name << " [" << domain.low << ", " << domain.high << "]" 
                                  << (isInt ? " (integer)" : "") << std::endl;
                    }
                } else {
                    // 对于全域搜索，使用更大的区间范围
                    if (config.use_global_search) {
                        if (config.verbose) {
                            std::cout << "Using global search interval for variable: " << var_name 
                                      << " " << (leftClosed ? "[" : "(") 
                                      << (std::isinf(domain.low) ? "-∞" : std::to_string(domain.low)) << ", " 
                                      << (std::isinf(domain.high) ? "∞" : std::to_string(domain.high)) 
                                      << (rightClosed ? "]" : ")") 
                                      << (isInt ? " (integer)" : "") << std::endl;
                        }
                    } else {
                        if (config.verbose) {
                            std::cout << "Using default interval for variable: " << var_name << " [" << domain.low << ", " << domain.high << "]" 
                                      << (isInt ? " (integer)" : "") << std::endl;
                        }
                    }
                }
                
                variables[var_name] = VariableConstraint(var_name, domain, isInt);
            }
        }
    }
    
    // Recursively process child nodes
    for (size_t i = 0; i < node->getChildrenSize(); ++i) {
        extractVariables(node->getChild(i));
    }
}

// Helper function to extract constant values from nodes
std::pair<bool, double> ICPSolver::getConstantValue(std::shared_ptr<SMTLIBParser::DAGNode> node) {
    if (node->isCInt() || node->isCReal()) {
        double value = 0.0;
        if (node->isCInt()) {
            value = parser->toInt(node).toDouble();
        } else if (node->isCReal()) {
            value = parser->toReal(node).toDouble();
        }
        return {true, value};
    }
    else if(node->isNeg() && node->getChildrenSize() == 1) {
        auto child = node->getChild(0);
        auto [isConstant, constant_val] = getConstantValue(child);
        if (isConstant) {
            return {true, -constant_val};
        }
    }
    return {false, 0.0};
}
