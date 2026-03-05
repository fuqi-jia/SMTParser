/* -*- Header -*-
 *
 * Context base and implementations for IR / Dispatcher
 *
 * Context: minimal abstraction for Dispatcher (virtual dtor only); no parser-specific
 *   interfaces; get* are only on ParserContext.
 * ParserContext: holds actual data and all get* (getAssertions, getAssumptions, etc.).
 * NullContext: empty context for dispatch(Node) default; no get*.
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

#ifndef CONTEXT_HEADER
#define CONTEXT_HEADER

#include "dag.h"
#include "objective.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SMTParser {

/**
 * Base context: polymorphic base for Dispatcher; handlers take (Node, Context&).
 * No parser-specific getters here; use ParserContext& when get* are needed.
 */
class Context {
public:
    virtual ~Context() = default;
};

/**
 * Context implementation that holds actual data (assertions, assumptions, etc.).
 * Used by Parser; parsing writes into this.
 */
class ParserContext : public Context {
public:
    std::vector<std::shared_ptr<DAGNode>> assertions;
    std::unordered_map<std::string, std::unordered_set<size_t>> assertion_groups;
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> named_assertions;
    std::vector<std::vector<std::shared_ptr<DAGNode>>> assumptions;
    std::vector<std::shared_ptr<DAGNode>> soft_assertions;
    std::vector<std::shared_ptr<DAGNode>> soft_weights;
    std::unordered_map<std::string, std::unordered_set<size_t>> soft_assertion_groups;
    std::vector<std::shared_ptr<Objective>> objectives;
    std::vector<std::shared_ptr<DAGNode>> split_lemmas;

    std::vector<std::shared_ptr<DAGNode>> getAssertions() const;
    std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedAssertions() const;
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> getNamedAssertions() const;
    std::vector<std::vector<std::shared_ptr<DAGNode>>> getAssumptions() const;
    std::vector<std::shared_ptr<DAGNode>> getSoftAssertions() const;
    std::vector<std::shared_ptr<DAGNode>> getSoftWeights() const;
    std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedSoftAssertions() const;
    std::vector<std::shared_ptr<Objective>> getObjectives() const;
    std::vector<std::shared_ptr<DAGNode>> getSplitLemmas() const;
};

/** Empty context for dispatch(Node) default; no get* (base has none). */
class NullContext : public Context {
};

} // namespace SMTParser

#endif
