/* -*- Source -*-
 *
 * An SMT/OMT Parser (Conversion part)
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

namespace SMTLIBParser {

    void Parser::collectAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_set<std::shared_ptr<DAGNode>>& atoms) {
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        collectAtoms(expr, atoms, visited);
    }

    void Parser::collectAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_set<std::shared_ptr<DAGNode>>& atoms, boost::unordered_set<std::shared_ptr<DAGNode>>& visited) {
        if (visited.find(expr) != visited.end()) {
            return;
        }
        visited.insert(expr);
        if (expr->isAtom()) {
            atoms.insert(expr);
        }
        for (size_t i = 0; i < expr->getChildrenSize(); i++) {
            collectAtoms(expr->getChild(i), atoms, visited);
        }
    }

    // // convert a list of expressions to CNF (a large AND node, whose children are all OR clauses)
    // std::shared_ptr<DAGNode> Parser::toCNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
    //     std::vector<std::shared_ptr<DAGNode>> new_cnf_children;
    //     // collect all atoms
    //     boost::unordered_set<std::shared_ptr<DAGNode>> atoms;
    //     for (auto& expr : exprs) {
    //         collectAtoms(expr, atoms);
    //     }

    //     // create a new variable for each atom
    //     boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> atom_map;
    //     for (auto& atom : atoms) {
    //         std::shared_ptr<DAGNode> new_var = mkVar(BOOL_SORT, atom->getName() + "_cnf");
    //         atom_map[atom] = new_var;
    //     }

    //     // use Tseitin transformation for each atom
    //     for(auto& atom : atoms){
    //         // not(atom) -> (new_var)
    //         new_cnf_children.emplace_back(mkOr({mkNot(atom), atom_map[atom]}));
    //         // (new_var) -> (atom)
    //         new_cnf_children.emplace_back(mkOr({mkNot(atom_map[atom]), atom}));
    //     }

    //     // create a new formula with Tseitin variables
    //     std::vector<std::shared_ptr<DAGNode>> new_exprs;
    //     for(auto& expr : exprs){
    //         std::shared_ptr<DAGNode> new_expr = replaceAtoms(expr, atom_map);
    //         new_exprs.emplace_back(new_expr);
    //     }


    //     // convert the new formula to CNF
    //     std::shared_ptr<DAGNode> cnf = toCNF(new_formula);

    //     // return the CNF
    //     return cnf;


    //     std::vector<std::shared_ptr<DAGNode>> clauses;
    //     for (auto& expr : exprs) {
    //         std::shared_ptr<DAGNode> cnf = toCNF(expr);
    //         if (cnf->isAnd()) {
    //             // add the children of the CNF (OR clauses) to the result
    //             for (size_t i = 0; i < cnf->getChildrenSize(); i++) {
    //                 clauses.emplace_back(cnf->getChild(i));
    //             }
    //         } else {
    //             // a single clause directly added
    //             clauses.emplace_back(cnf);
    //         }
    //     }
    //     // if there is only one clause, return it directly
    //     if (clauses.size() == 1) {
    //         return clauses[0];
    //     }
    //     // otherwise, create an AND node, containing all OR clauses
    //     return mkAnd(clauses);
    // }

    
    // // convert a single expression to CNF
    // std::shared_ptr<DAGNode> Parser::toCNF(std::shared_ptr<DAGNode> expr) {
    //     // first convert to NNF
    //     std::shared_ptr<DAGNode> nnf_expr = toNNF(expr);
        
    //     // if the expression is already an atom or its negation
    //     if (expr->isAtom()) {
    //         // atom is regarded as a single clause of CNF
    //         std::vector<std::shared_ptr<DAGNode>> clause;
    //         clause.emplace_back(nnf_expr);
    //         return mkOr(clause);
    //     }
        
    //     // if the expression is AND
    //     if (nnf_expr->isAnd()) {
    //         std::vector<std::shared_ptr<DAGNode>> clauses;
    //         for (size_t i = 0; i < nnf_expr->getChildrenSize(); i++) {
    //             std::shared_ptr<DAGNode> child_cnf = toCNF(nnf_expr->getChild(i));
    //             if (child_cnf->isAnd()) {
    //                 // add all children of the child CNF to the result
    //                 for (size_t j = 0; j < child_cnf->getChildrenSize(); j++) {
    //                     clauses.emplace_back(child_cnf->getChild(j));
    //                 }
    //             } else {
    //                 // add a single clause
    //                 clauses.emplace_back(child_cnf);
    //             }
    //         }
    //         return mkAnd(clauses);
    //     }
        
    //     // if the expression is OR
    //     if (nnf_expr->isOr()) {
    //         // collect CNF forms of all children of OR
    //         std::vector<std::shared_ptr<DAGNode>> child_cnfs;
    //         for (size_t i = 0; i < nnf_expr->getChildrenSize(); i++) {
    //             child_cnfs.emplace_back(toCNF(nnf_expr->getChild(i)));
    //         }
            
    //         // apply distributive law: (A∨B)∧(C∨D) -> (A∨B∨C∨D)
    //         return applyCNFDistributiveLaw(child_cnfs);
    //     }
        
    //     // other types of nodes remain unchanged
    //     return nnf_expr;
    // }

    // std::shared_ptr<DAGNode> Parser::toCNF(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& cache) {
    //     if (cache.find(expr) != cache.end()) {
    //         return cache[expr];
    //     }
    //     // Tseitin transformation
    //     std::shared_ptr<DAGNode> result = toCNF(expr);
    //     cache[expr] = result;
    //     return result;
    // }

    // // convert a list of expressions to DNF (a large OR node, whose children are all AND terms)
    // std::shared_ptr<DAGNode> Parser::toDNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
    //     std::vector<std::shared_ptr<DAGNode>> terms;
    //     for (auto& expr : exprs) {
    //         std::shared_ptr<DAGNode> dnf = toDNF(expr);
    //         if (dnf->isOr()) {
    //             // add the children of the DNF (AND terms) to the result
    //             for (size_t i = 0; i < dnf->getChildrenSize(); i++) {
    //                 terms.emplace_back(dnf->getChild(i));
    //             }
    //         } else {
    //             // a single term directly added
    //             terms.emplace_back(dnf);
    //         }
    //     }
    //     // if there is only one term, return it directly
    //     if (terms.size() == 1) {
    //         return terms[0];
    //     }
    //     // otherwise, create an OR node, containing all AND terms
    //     return mkOr(terms);
    // }

    
    // // auxiliary function: apply CNF distributive law
    // std::shared_ptr<DAGNode> Parser::applyCNFDistributiveLaw(const std::vector<std::shared_ptr<DAGNode>>& child_cnfs) {
    //     if (child_cnfs.empty()) {
    //         return mkTrue();
    //     }
        
    //     // 开始应用分配律
    //     std::shared_ptr<DAGNode> result = child_cnfs[0];
        
    //     for (size_t i = 1; i < child_cnfs.size(); i++) {
    //         std::shared_ptr<DAGNode> next = child_cnfs[i];
    //         std::vector<std::shared_ptr<DAGNode>> new_clauses;
            
    //         // 对result的每个子句
    //         std::vector<std::shared_ptr<DAGNode>> result_clauses;
    //         if (result->isAnd()) {
    //             for (size_t j = 0; j < result->getChildrenSize(); j++) {
    //                 result_clauses.emplace_back(result->getChild(j));
    //             }
    //         } else {
    //             result_clauses.emplace_back(result);
    //         }
            
    //         // 对next的每个子句
    //         std::vector<std::shared_ptr<DAGNode>> next_clauses;
    //         if (next->isAnd()) {
    //             for (size_t j = 0; j < next->getChildrenSize(); j++) {
    //                 next_clauses.emplace_back(next->getChild(j));
    //             }
    //         } else {
    //             next_clauses.emplace_back(next);
    //         }
            
    //         // 应用分配律: (A∨B)∧(C∨D) -> (A∨C)∧(A∨D)∧(B∨C)∧(B∨D)
    //         for (auto& result_clause : result_clauses) {
    //             for (auto& next_clause : next_clauses) {
    //                 std::vector<std::shared_ptr<DAGNode>> combined_literals;
                    
    //                 // 收集result_clause中的所有文字
    //                 if (result_clause->isOr()) {
    //                     for (size_t j = 0; j < result_clause->getChildrenSize(); j++) {
    //                         combined_literals.emplace_back(result_clause->getChild(j));
    //                     }
    //                 } else {
    //                     combined_literals.emplace_back(result_clause);
    //                 }
                    
    //                 // 收集next_clause中的所有文字
    //                 if (next_clause->isOr()) {
    //                     for (size_t j = 0; j < next_clause->getChildrenSize(); j++) {
    //                         combined_literals.emplace_back(next_clause->getChild(j));
    //                     }
    //                 } else {
    //                     combined_literals.emplace_back(next_clause);
    //                 }
                    
    //                 // 创建新的OR子句
    //                 new_clauses.emplace_back(mkOr(combined_literals));
    //             }
    //         }
            
    //         // 更新result为新子句的AND
    //         result = mkAnd(new_clauses);
    //     }
        
    //     return result;
    // }

    // // convert a single expression to DNF
    // std::shared_ptr<DAGNode> Parser::toDNF(std::shared_ptr<DAGNode> expr) {
    //     // first convert to NNF
    //     std::shared_ptr<DAGNode> nnf_expr = toNNF(expr);
        
    //     // if the expression is already an atom or its negation
    //     if (nnf_expr->isCBool() || nnf_expr->isVBool() || 
    //         (nnf_expr->isNot() && (nnf_expr->getChild(0)->isCBool() || nnf_expr->getChild(0)->isVBool()))) {
    //         // atom is regarded as a single term of DNF
    //         std::vector<std::shared_ptr<DAGNode>> term;
    //         term.emplace_back(nnf_expr);
    //         return mkAnd(term);
    //     }
        
    //     // if the expression is OR
    //     if (nnf_expr->isOr()) {
    //         std::vector<std::shared_ptr<DAGNode>> terms;
    //         for (size_t i = 0; i < nnf_expr->getChildrenSize(); i++) {
    //             std::shared_ptr<DAGNode> child_dnf = toDNF(nnf_expr->getChild(i));
    //             if (child_dnf->isOr()) {
    //                 // add all terms of the child DNF to the result
    //                 for (size_t j = 0; j < child_dnf->getChildrenSize(); j++) {
    //                     terms.emplace_back(child_dnf->getChild(j));
    //                 }
    //             } else {
    //                 // add a single term
    //                 terms.emplace_back(child_dnf);
    //             }
    //         }
    //         return mkOr(terms);
    //     }
        
    //     // if the expression is AND
    //     if (nnf_expr->isAnd()) {
    //         // collect DNF forms of all children of AND
    //         std::vector<std::shared_ptr<DAGNode>> child_dnfs;
    //         for (size_t i = 0; i < nnf_expr->getChildrenSize(); i++) {
    //             child_dnfs.emplace_back(toDNF(nnf_expr->getChild(i)));
    //         }
            
    //         // apply distributive law: (A∧B)∨(C∧D) -> (A∧B∧C∧D)
    //         return applyDNFDistributiveLaw(child_dnfs);
    //     }
        
    //     // other types of nodes remain unchanged
    //     return nnf_expr;
    // }
    
    // // apply DNF distributive law
    // std::shared_ptr<DAGNode> Parser::applyDNFDistributiveLaw(const std::vector<std::shared_ptr<DAGNode>>& child_dnfs) {
    //     if (child_dnfs.empty()) {
    //         return mkFalse();
    //     }
        
    //     // start applying distributive law
    //     std::shared_ptr<DAGNode> result = child_dnfs[0];
        
    //     for (size_t i = 1; i < child_dnfs.size(); i++) {
    //         std::shared_ptr<DAGNode> next = child_dnfs[i];
    //         std::vector<std::shared_ptr<DAGNode>> new_terms;
            
    //         // for each term of result
    //         std::vector<std::shared_ptr<DAGNode>> result_terms;
    //         if (result->isOr()) {
    //             for (size_t j = 0; j < result->getChildrenSize(); j++) {
    //                 result_terms.emplace_back(result->getChild(j));
    //             }
    //         } else {
    //             result_terms.emplace_back(result);
    //         }
            
    //         // for each term of next
    //         std::vector<std::shared_ptr<DAGNode>> next_terms;
    //         if (next->isOr()) {
    //             for (size_t j = 0; j < next->getChildrenSize(); j++) {
    //                 next_terms.emplace_back(next->getChild(j));
    //             }
    //         } else {
    //             next_terms.emplace_back(next);
    //         }
            
    //         // apply distributive law: (A∧B)∨(C∧D) -> (A∧C)∨(A∧D)∨(B∧C)∨(B∧D)
    //         for (auto& result_term : result_terms) {
    //             for (auto& next_term : next_terms) {
    //                 std::vector<std::shared_ptr<DAGNode>> combined_literals;
                    
    //                 // collect all literals in result_term
    //                 if (result_term->isAnd()) {
    //                     for (size_t j = 0; j < result_term->getChildrenSize(); j++) {
    //                         combined_literals.emplace_back(result_term->getChild(j));
    //                     }
    //                 } else {
    //                     combined_literals.emplace_back(result_term);
    //                 }
                    
    //                 // collect all literals in next_term
    //                 if (next_term->isAnd()) {
    //                     for (size_t j = 0; j < next_term->getChildrenSize(); j++) {
    //                         combined_literals.emplace_back(next_term->getChild(j));
    //                     }
    //                 } else {
    //                     combined_literals.emplace_back(next_term);
    //                 }
                    
    //                 // create a new AND term
    //                 new_terms.emplace_back(mkAnd(combined_literals));
    //             }
    //         }
            
    //         // update result to be the OR of new terms
    //         result = mkOr(new_terms);
    //     }
        
    //     return result;
    // }

    // convert a list of expressions to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
        std::vector<std::shared_ptr<DAGNode>> nnf_nodes;
        for (auto& expr : exprs) {
            nnf_nodes.emplace_back(toNNF(expr));
        }
        // if there is only one expression, return it directly
        if (nnf_nodes.size() == 1) {
            return nnf_nodes[0];
        }
        // otherwise, create an AND node, containing all NNF expressions
        return mkAnd(nnf_nodes);
    }

    // convert a single expression to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::shared_ptr<DAGNode> expr, bool is_not) {
        // handle constants and variables
        if(expr->isCBool() || expr->isVBool()){
            if(is_not){
                return mkNot(expr);
            }
            return expr;
        }
        
        // handle NOT node
        if(expr->isNot()){
            // negate propagation: ¬¬A → A
            return toNNF(expr->getChild(0), !is_not);
        }
        
        // handle AND node
        if(expr->isAnd()){
            std::vector<std::shared_ptr<DAGNode>> children;
            for(size_t i = 0; i < expr->getChildrenSize(); i++){
                // recursively handle each child node
                children.emplace_back(toNNF(expr->getChild(i), is_not));
            }
            
            // apply De Morgan's law based on is_not: ¬(A∧B) → (¬A∨¬B)
            if(is_not){
                return mkOr(children);
            } else {
                return mkAnd(children);
            }
        }
        
        // handle OR node
        if(expr->isOr()){
            std::vector<std::shared_ptr<DAGNode>> children;
            for(size_t i = 0; i < expr->getChildrenSize(); i++){
                // recursively handle each child node
                children.emplace_back(toNNF(expr->getChild(i), is_not));
            }
            
            // apply De Morgan's law based on is_not: ¬(A∨B) → (¬A∧¬B)
            if(is_not){
                return mkAnd(children);
            } else {
                return mkOr(children);
            }
        }
        
        // handle IMPLIES node
        if(expr->isImplies()){
            std::shared_ptr<DAGNode> A = expr->getChild(0);
            std::shared_ptr<DAGNode> B = expr->getChild(1);
            
            if(is_not){
                // ¬(A→B) → (A∧¬B)
                return mkAnd({toNNF(A, false), toNNF(B, true)});
            } else {
                // A→B → (¬A∨B)
                return mkOr({toNNF(A, true), toNNF(B, false)});
            }
        }
        
        // handle ITE node (conditional expression)
        if(expr->isIte() && expr->getChild(1)->getSort()->isBool()){
            std::shared_ptr<DAGNode> A = expr->getChild(0);  // condition
            std::shared_ptr<DAGNode> B = expr->getChild(1);  // then branch
            std::shared_ptr<DAGNode> C = expr->getChild(2);  // else branch
            
            if(is_not){
                // ¬(if A then B else C) → (A∧¬B)∨(¬A∧¬C)
                return mkOr({
                    mkAnd({toNNF(A, false), toNNF(B, true)}),
                    mkAnd({toNNF(A, true), toNNF(C, true)})
                });
            } else {
                // if A then B else C → (A∧B)∨(¬A∧C)
                return mkOr({
                    mkAnd({toNNF(A, false), toNNF(B, false)}),
                    mkAnd({toNNF(A, true), toNNF(C, false)})
                });
            }
        }
        
        // handle other types of nodes (e.g., arithmetic operators)
        if(is_not){
            return negateAtom(expr);
        }
        return expr;
    }

    // convert a single expression to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::shared_ptr<DAGNode> expr) {
        return toNNF(expr, false);
    }
}
