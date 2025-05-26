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

    SMTInterval::SMTInterval(std::shared_ptr<Parser> parser, std::shared_ptr<DAGNode> lower, std::shared_ptr<DAGNode> upper, bool leftClosed, bool rightClosed)
        : parser(parser), lower(lower), upper(upper), leftClosed(leftClosed), rightClosed(rightClosed) {}

    SMTLIBInterval::SMTLIBInterval(const Interval& interval)
        : interval(interval) {}

    SMTLIBInterval::~SMTLIBInterval() {}

    SMTLIBInterval& SMTLIBInterval::operator=(const SMTLIBInterval& other) {
        if(this != &other) {
            parser = other.parser;
            lower = other.lower;
            upper = other.upper;
            leftClosed = other.leftClosed;
            rightClosed = other.rightClosed;
        }
        return *this;
    }

    bool SMTLIBInterval::operator==(const SMTLIBInterval& other) const {
        return lower == other.lower && upper == other.upper && leftClosed == other.leftClosed && rightClosed == other.rightClosed;
    }

    bool SMTLIBInterval::operator!=(const SMTLIBInterval& other) const {
        return !(*this == other);
    }

    bool SMTLIBInterval::setLower(std::shared_ptr<DAGNode> lower) {
        lower = lower;
        return true;
    }

    bool SMTLIBInterval::setUpper(std::shared_ptr<DAGNode> upper) {
        upper = upper;
        return true;
    }

    bool SMTLIBInterval::setLeftClosed(bool leftClosed) {
        leftClosed = leftClosed;
        return true;
    }

    bool SMTLIBInterval::setRightClosed(bool rightClosed) {
        rightClosed = rightClosed;
        return true;
    }

    bool SMTLIBInterval::isLeftClosed() const {
        return leftClosed;
    }

    bool SMTLIBInterval::isRightClosed() const {
        return rightClosed;
    }

    bool SMTLIBInterval::isLeftUnbounded() const {
        return lower->isInfinity();
    }

    bool SMTLIBInterval::isRightUnbounded() const {
        return upper->isInfinity();
    }

    std::shared_ptr<DAGNode> SMTLIBInterval::midpoint() const {
        return parser->mkDiv(parser->mkAdd(lower, upper), parser->mkInt(2));
    }
    std::string SMTLIBInterval::toString() const {
        std::stringstream ss;
        ss << "[" << (leftClosed ? "[" : "]") << parser->toString(lower) << ", " << parser->toString(upper) << (rightClosed ? "]" : "]");
        return ss.str();
    }

    


} // namespace SMTLIBParser
