/* -*- Header -*-
 *
 * Context base and implementations for IR / Dispatcher
 *
 * Context: base holding managers (NodeManager, SortManager, SymbolManager, ObjectiveManager, Options).
 * ParserContext: extends Context with assertions, assumptions, etc.
 * NullContext: empty context for dispatch(Node) default; managers remain nullptr.
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
#include "options.h"
#include "symbol_manager.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SMTParser {

/**
 * Base context: holds managers and options; polymorphic base for Dispatcher.
 * Handlers take (Node, Context&); get* for managers are here.
 */
class Context {
protected:
    std::shared_ptr<NodeManager>   node_manager_;
    std::shared_ptr<SortManager>    sort_manager_;
    std::shared_ptr<SymbolManager>  symbol_manager_;
    std::shared_ptr<ObjectiveManager> objective_manager_;
    std::shared_ptr<GlobalOptions>  options_;

public:
    virtual ~Context() = default;

    void setNodeManager(std::shared_ptr<NodeManager> nm) { node_manager_ = std::move(nm); }
    void setSortManager(std::shared_ptr<SortManager> sm) { sort_manager_ = std::move(sm); }
    void setSymbolManager(std::shared_ptr<SymbolManager> sm) { symbol_manager_ = std::move(sm); }
    void setObjectiveManager(std::shared_ptr<ObjectiveManager> om) { objective_manager_ = std::move(om); }
    void setOptions(std::shared_ptr<GlobalOptions> opt) { options_ = std::move(opt); }

    std::shared_ptr<NodeManager> getNodeManager() { return node_manager_; }
    std::shared_ptr<NodeManager> getNodeManager() const { return node_manager_; }
    std::shared_ptr<SortManager> getSortManager() { return sort_manager_; }
    std::shared_ptr<SortManager> getSortManager() const { return sort_manager_; }
    std::shared_ptr<SymbolManager> getSymbolManager() { return symbol_manager_; }
    std::shared_ptr<SymbolManager> getSymbolManager() const { return symbol_manager_; }
    std::shared_ptr<ObjectiveManager> getObjectiveManager() { return objective_manager_; }
    std::shared_ptr<ObjectiveManager> getObjectiveManager() const { return objective_manager_; }
    std::shared_ptr<GlobalOptions> getOptions() { return options_; }
    std::shared_ptr<GlobalOptions> getOptions() const { return options_; }
};

/**
 * Context implementation that holds parser data (assertions, assumptions, etc.).
 * Inherits managers and options from Context; used by Parser.
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
