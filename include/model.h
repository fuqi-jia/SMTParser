/* -*- Header -*-
 *
 * The Model Enumeration
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

#ifndef _MODEL_H
#define _MODEL_H

#include "dag.h"

namespace SMTLIBParser{
    class Model{
        public:
            Model();
            ~Model();
            void add(const std::shared_ptr<DAGNode> &node, const std::shared_ptr<DAGNode> &value);
            void add(const std::string &name, const std::shared_ptr<DAGNode> &value);
            void addVar(const std::shared_ptr<DAGNode> &node);
            std::shared_ptr<DAGNode> getValue(const std::shared_ptr<DAGNode> &node);
            std::shared_ptr<DAGNode> getValue(const std::string &name);
            bool isFull() const;
            
            std::string toString();
        private:
            std::unordered_map<std::string, size_t> model_name_index;
            std::vector<std::shared_ptr<DAGNode>> model_vars;
            std::vector<std::shared_ptr<DAGNode>> model_values;
    };
}

#endif

