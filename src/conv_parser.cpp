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

    std::shared_ptr<DAGNode> Parser::replaceAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map) {
        boost::unordered_set<std::shared_ptr<DAGNode>> visited;
        bool is_changed = false;
        std::shared_ptr<DAGNode> new_expr = replaceAtoms(expr, atom_map, visited, is_changed);
        if (is_changed) {
            return new_expr;
        }
        return expr;
    }

    std::shared_ptr<DAGNode> Parser::replaceAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, bool& is_changed) {
        if (visited.find(expr) != visited.end()) {
            return visited[expr];
        }
        if (expr->isAtom() && atom_map.find(expr) != atom_map.end()) {
            is_changed = true;
            visited[expr] = atom_map[expr];
            return atom_map[expr];
        }
        std::vector<std::shared_ptr<DAGNode>> children;
        for (size_t i = 0; i < expr->getChildrenSize(); i++) {
            bool child_is_changed = false;
            std::shared_ptr<DAGNode> child_expr = replaceAtoms(expr->getChild(i), atom_map, visited, child_is_changed);
            if (child_is_changed) {
                is_changed = true;
            }
            children.emplace_back(child_expr);
        }
        if (is_changed) {
            std::shared_ptr<DAGNode> new_expr = mkOper(expr->getSort(), expr->getKind(), children);
            visited[expr] = new_expr; // no need to visit again
            return new_expr;
        }
        assert(!is_changed);
        visited[expr] = expr;
        return expr;
    }

    std::shared_ptr<DAGNode> Parser::toTseitinCNF(std::shared_ptr<DAGNode> expr, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        std::shared_ptr<DAGNode> result = toTseitinCNF(expr, visited, clauses);
        return result;
    }
    std::shared_ptr<DAGNode> Parser::toTseitinXor(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        // c <-> a xor b <=> (c -> a xor b) and (a xor b -> c)
        // => c -> a xor b => ¬c or a xor b => ¬c or ((¬a or ¬b) and (a or b))
        //    => (¬c or ¬a or ¬b) and (¬c or a or b)
        // => a xor b -> c => ¬((¬a and b) or (a and ¬b)) or c => (a or ¬b) and (¬a or b) -> c
        //    => (a or ¬b or c) and (¬a or b or c)
        std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
        // -a -b -c
        std::vector<std::shared_ptr<DAGNode>> or_children1;
        or_children1.emplace_back(mkNot(c));
        or_children1.emplace_back(mkNot(a));
        or_children1.emplace_back(mkNot(b));
        clauses.emplace_back(mkOr(or_children1));
        // a b -c
        std::vector<std::shared_ptr<DAGNode>> or_children2;
        or_children2.emplace_back(mkNot(c));
        or_children2.emplace_back(a);
        or_children2.emplace_back(b);
        clauses.emplace_back(mkOr(or_children2));
        // -a b c
        std::vector<std::shared_ptr<DAGNode>> or_children3;
        or_children3.emplace_back(c);
        or_children3.emplace_back(mkNot(a));
        or_children3.emplace_back(b);
        clauses.emplace_back(mkOr(or_children3));
        // a -b c
        std::vector<std::shared_ptr<DAGNode>> or_children4;
        or_children4.emplace_back(c);
        or_children4.emplace_back(a);
        or_children4.emplace_back(mkNot(b));
        clauses.emplace_back(mkOr(or_children4));
        visited[expr] = c;
        assert(c->isLiteral());
        return c;
    }
    // auxiliary function: handle the equivalence relation between two boolean variables
    std::shared_ptr<DAGNode> Parser::toTseitinEq(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
        
        // c <-> (a <-> b) -> c -> (a <-> b) and (a <-> b) -> c
        // => (¬c or a or ¬b) and (¬c or ¬a or b) and (c or a or b) and (c or ¬a or ¬b)
        
        // add clause: (¬c ∨ a ∨ ¬b) - when a is false or b is true, c can be false
        clauses.emplace_back(mkOr({mkNot(c), a, mkNot(b)}));
        
        // add clause: (¬c ∨ ¬a ∨ b) - when a is true or b is false, c can be false
        clauses.emplace_back(mkOr({mkNot(c), mkNot(a), b}));
        
        // add clause: (c ∨ a ∨ b) - when a and b are both false, c must be true
        clauses.emplace_back(mkOr({c, a, b}));
        
        // add clause: (c ∨ ¬a ∨ ¬b) - when a and b are both true, c must be true
        clauses.emplace_back(mkOr({c, mkNot(a), mkNot(b)}));
        
        return c;
    }

    // auxiliary function: handle the inequality relation between two boolean variables
    std::shared_ptr<DAGNode> Parser::toTseitinDistinct(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
        
        // c <-> (a != b) -> c -> (a != b)
        // => (¬c or a or b) and (¬c or ¬a or ¬b) and (c or ¬a or b) and (c or a or ¬b)
        
        // add clause: (¬c ∨ a ∨ b) - when a and b are both false, c can be false
        clauses.emplace_back(mkOr({mkNot(c), a, b}));
        
        // add clause: (¬c ∨ ¬a ∨ ¬b) - when a and b are both true, c can be false
        clauses.emplace_back(mkOr({mkNot(c), mkNot(a), mkNot(b)}));
        
        // add clause: (c ∨ ¬a ∨ b) - when a is true and b is false, c must be true
        clauses.emplace_back(mkOr({c, mkNot(a), b}));
        
        // add clause: (c ∨ a ∨ ¬b) - when a is false and b is true, c must be true
        clauses.emplace_back(mkOr({c, a, mkNot(b)}));
        
        return c;
    }
    std::shared_ptr<DAGNode> Parser::toTseitinCNF(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        // Tseitin CNF is ¬applied to atoms: all atoms are already in CNF form
        assert(!expr->isAtom());
        if (visited.find(expr) != visited.end()) {
            return visited[expr];
        }
        if(expr->isLiteral()) {
            // always return the original expression
            // and no need to add to visited
            return expr;
        }
        // a and b and ... <=> c <-> a and b and ...
        // => c -> a and b and ... => ¬c or a and b and ... => (¬c or a) and (¬c or b) and ...
        // => a and b and ... -> c => ¬a or ¬b or ... or c
        if (expr->isAnd()) {
            std::vector<std::shared_ptr<DAGNode>> children;
            for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                std::shared_ptr<DAGNode> child_cnf = toTseitinCNF(expr->getChild(i), visited, clauses);
                children.emplace_back(child_cnf);
            }
            if(children.size() == 1){
                // return the only child, which is a temp var or boolean variable
                assert(children[0]->isLiteral());
                return children[0];
            }
            std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
            std::vector<std::shared_ptr<DAGNode>> or_children;
            for(auto& child : children) {
                clauses.emplace_back(mkOr({mkNot(c), child}));
                or_children.emplace_back(mkNot(child));
            }
            or_children.emplace_back(c);
            clauses.emplace_back(mkOr(or_children));
            visited[expr] = c; // no need to visit again
            assert(c->isLiteral());
            return c;
        }
        // a or b or ... <=> c <-> a or b or ...
        // => c -> a or b or ... => ¬c or a or b or ... => ¬c or a or b or ...
        // => a or b or ... -> c => (¬a and ¬b and ...) or c => ¬a or c and ¬b or c and ...
        else if (expr->isOr()) {
            std::vector<std::shared_ptr<DAGNode>> children;
            for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                std::shared_ptr<DAGNode> child_cnf = toTseitinCNF(expr->getChild(i), visited, clauses);
                children.emplace_back(child_cnf);
            }
            if(children.size() == 1){
                // return the only child, which is a temp var or boolean variable
                assert(children[0]->isLiteral());
                return children[0];
            }
            std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
            std::vector<std::shared_ptr<DAGNode>> or_children;
            for(auto& child : children) {
                clauses.emplace_back(mkOr({mkNot(child), c}));
                or_children.emplace_back(child);
            }
            or_children.emplace_back(mkNot(c));
            clauses.emplace_back(mkOr(or_children));
            visited[expr] = c; // no need to visit again
            assert(c->isLiteral());
            return c;
        }
        // c <-> a -> b <=> c -> a -> b and a -> b -> c
        // => c -> a -> b => ¬c or ¬a or b
        // => a -> b -> c => ¬a or ¬b or c
        else if (expr->isImplies()) {
            std::vector<std::shared_ptr<DAGNode>> children;
            for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                std::shared_ptr<DAGNode> child_cnf = toTseitinCNF(expr->getChild(i), visited, clauses);
                children.emplace_back(child_cnf);
            }
            if(children.size() == 1){
                // return the only child, which is a temp var or boolean variable
                assert(children[0]->isLiteral());
                return children[0];
            }
            std::shared_ptr<DAGNode> c = mkTempVar(BOOL_SORT);
            std::vector<std::shared_ptr<DAGNode>> or_children1;
            std::vector<std::shared_ptr<DAGNode>> or_children2;
            or_children1.emplace_back(mkNot(c));
            for(size_t i = 0; i < children.size(); i++) {
                if(i == children.size() - 1){
                    or_children1.emplace_back(children[i]);
                } else {
                    or_children1.emplace_back(mkNot(children[i]));
                }
                or_children2.emplace_back(mkNot(children[i]));
            }
            or_children2.emplace_back(c);
            clauses.emplace_back(mkOr(or_children1));
            clauses.emplace_back(mkOr(or_children2));
            visited[expr] = c; // no need to visit again
            assert(c->isLiteral());
            return c;
        }
        // c <-> a xor b <=> (c -> a xor b) and (a xor b -> c)
        // => c -> a xor b => ¬c or a xor b => ¬c or ((¬a or ¬b) and (a or b))
        //    => (¬c or ¬a or ¬b) and (¬c or a or b)
        // => a xor b -> c => ¬((¬a and b) or (a and ¬b)) or c => (a or ¬b) and (¬a or b) -> c
        //    => (a or ¬b or c) and (¬a or b or c)
        else if (expr->isXor()) {
            std::vector<std::shared_ptr<DAGNode>> children;
            if(expr->getChildrenSize() == 1){
                std::shared_ptr<DAGNode> child_cnf = toTseitinCNF(expr->getChild(0), visited, clauses);
                visited[expr] = child_cnf;
                assert(child_cnf->isLiteral());
                return child_cnf;
            }
            else if(expr->getChildrenSize() == 2){
                std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
                std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(1), visited, clauses);
                std::shared_ptr<DAGNode> c = toTseitinXor(a, b, clauses);
                visited[expr] = c;
                assert(c->isLiteral());
                return c;
            }
            else{
                std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
                for(size_t i = 1; i < expr->getChildrenSize(); i++){
                    std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(i), visited, clauses);
                    a = toTseitinXor(a, b, clauses);
                }
                visited[expr] = a;
                assert(a->isLiteral());
                return a;
            }
        }
        else if(expr->isEq()){
            // all children are boolean variables
            bool all_bool = true;
            for(size_t i = 0; i < expr->getChildrenSize(); i++){
                if(!expr->getChild(i)->getSort()->isBool()){
                    all_bool = false;
                    err_all(ERROR_TYPE::ERR_TYPE_MISMATCH, "boolean", expr->getChild(i)->getSort()->toString());
                    break;
                }
            }

            assert(all_bool);
            
            if(all_bool){
                if(expr->getChildrenSize() == 1){
                    // directly return the only child
                    std::shared_ptr<DAGNode> child_cnf = toTseitinCNF(expr->getChild(0), visited, clauses);
                    visited[expr] = child_cnf;
                    return child_cnf;
                }
                else if(expr->getChildrenSize() == 2){
                    // two children
                    std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
                    std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(1), visited, clauses);
                    std::shared_ptr<DAGNode> c = toTseitinEq(a, b, clauses);
                    visited[expr] = c;
                    assert(c->isLiteral());
                    return c;
                }
                else{
                    // multiple children
                    std::vector<std::shared_ptr<DAGNode>> eq_results;
                    std::shared_ptr<DAGNode> first = toTseitinCNF(expr->getChild(0), visited, clauses);
                    
                    for(size_t i = 1; i < expr->getChildrenSize(); i++){
                        std::shared_ptr<DAGNode> next = toTseitinCNF(expr->getChild(i), visited, clauses);
                        eq_results.emplace_back(toTseitinEq(first, next, clauses));
                    }
                    
                    // combine all equalities using AND
                    std::shared_ptr<DAGNode> result = mkTempVar(BOOL_SORT);
                    
                    // add the equivalence relation clauses
                    // result -> (eq1 ∧ eq2 ∧ ... ∧ eqn)
                    // => ¬result ∨ (eq1 ∧ eq2 ∧ ... ∧ eqn)
                    // => (¬result ∨ eq1) ∧ (¬result ∨ eq2) ∧ ... ∧ (¬result ∨ eqn)
                    for(auto& eq : eq_results){
                        clauses.emplace_back(mkOr({mkNot(result), eq}));
                    }
                    
                    // (eq1 ∧ eq2 ∧ ... ∧ eqn) -> result
                    // => ¬(eq1 ∧ eq2 ∧ ... ∧ eqn) ∨ result
                    // => (¬eq1 ∨ ¬eq2 ∨ ... ∨ ¬eqn) ∨ result
                    std::vector<std::shared_ptr<DAGNode>> or_children;
                    for(auto& eq : eq_results){
                        or_children.emplace_back(mkNot(eq));
                    }
                    or_children.emplace_back(result);
                    clauses.emplace_back(mkOr(or_children));
                    
                    visited[expr] = result;
                    assert(result->isLiteral());
                    return result;
                }
            }
        }
        else if(expr->isDistinct() && expr->getChild(0)->getSort()->isBool() && expr->getChild(1)->getSort()->isBool()){
            // ensure all children are boolean
            bool all_bool = true;
            for(size_t i = 0; i < expr->getChildrenSize(); i++){
                if(!expr->getChild(i)->getSort()->isBool()){
                    all_bool = false;
                    break;
                }
            }
            
            if(all_bool){
                // handle boolean inequality
                if(expr->getChildrenSize() == 1){
                    // single child, meaningless, return true
                    err_all(ERROR_TYPE::ERR_TYPE_MISMATCH, "distinct with 1 variable is meaningless");
                    return mkTrue();
                }
                else if(expr->getChildrenSize() == 2){
                    // two children
                    std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
                    std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(1), visited, clauses);
                    std::shared_ptr<DAGNode> c = toTseitinDistinct(a, b, clauses);
                    visited[expr] = c;
                    assert(c->isLiteral());
                    return c;
                }
                else{
                    // for boolean variables, distinct with more than 2 variables is always unsatisfiable
                    // because boolean values can only be true or false
                    std::cerr << "toTseitinCNF: distinct with more than 2 variables is always unsatisfiable" << std::endl;
                    return mkFalse();
                }
            }
        }
        else if(expr->isITE() && expr->getChild(1)->getSort()->isBool() && expr->getChild(2)->getSort()->isBool()){
            // handle condition expression: if a then b else c
            std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
            std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(1), visited, clauses);
            std::shared_ptr<DAGNode> c = toTseitinCNF(expr->getChild(2), visited, clauses);
            std::shared_ptr<DAGNode> d = mkTempVar(BOOL_SORT);
            
            // add clause: (¬d ∨ ¬a ∨ b) - when a is true, d must be the same as b
            clauses.emplace_back(mkOr({mkNot(d), mkNot(a), b}));
            
            // add clause: (¬d ∨ a ∨ c) - when a is false, d must be the same as c
            clauses.emplace_back(mkOr({mkNot(d), a, c}));
            
            // add clause: (d ∨ ¬a ∨ ¬b) - when a is true and b is true, d must be true
            clauses.emplace_back(mkOr({d, mkNot(a), mkNot(b)}));
            
            // add clause: (d ∨ a ∨ ¬c) - when a is false and c is false, d must be true
            clauses.emplace_back(mkOr({d, a, mkNot(c)}));
            
            visited[expr] = d;
            assert(d->isLiteral());
            return d;
        }
        else{
            err_all(ERROR_TYPE::ERR_TYPE_MISMATCH, "unsupported node type: " + kindToString(expr->getKind()));
            return mkFalse();
        }

        return expr;
    }
    
    

    // convert a list of expressions to CNF (a large AND node, whose children are all OR clauses)
    std::shared_ptr<DAGNode> Parser::toCNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
        std::vector<std::shared_ptr<DAGNode>> clauses;
        // collect all atoms
        boost::unordered_set<std::shared_ptr<DAGNode>> atoms;
        for (auto& expr : exprs) {
            collectAtoms(expr, atoms);
        }

        // create a new variable for each atom
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> atom_map;
        for (auto& atom : atoms) {
            std::shared_ptr<DAGNode> new_var = mkTempVar(BOOL_SORT);
            atom_map[atom] = new_var;
        }

        // use Tseitin transformation for each atom
        for(auto& atom : atoms){
            // not(atom) -> (new_var)
            clauses.emplace_back(mkOr({mkNot(atom), atom_map[atom]}));
            // (new_var) -> (atom)
            clauses.emplace_back(mkOr({mkNot(atom_map[atom]), atom}));
        }

        // create a new formula with Tseitin variables
        std::vector<std::shared_ptr<DAGNode>> new_exprs;
        for(auto& expr : exprs){
            std::shared_ptr<DAGNode> new_expr = replaceAtoms(expr, atom_map);
            new_exprs.emplace_back(new_expr);
        }

        // currently, the new formula has only boolean variables
        for (auto& expr : new_exprs) {
            std::shared_ptr<DAGNode> tseitin_cnf = toTseitinCNF(expr, clauses);
            clauses.emplace_back(tseitin_cnf);
        }

        // if there is only one clause, return it directly
        if (clauses.size() == 1) {
            return clauses[0];
        }
        // otherwise, create an AND node, containing all OR clauses
        return mkAnd(clauses);
    }

    
    // convert a single expression to CNF
    std::shared_ptr<DAGNode> Parser::toCNF(std::shared_ptr<DAGNode> expr) {
        std::vector<std::shared_ptr<DAGNode>> clauses;
        // collect all atoms
        boost::unordered_set<std::shared_ptr<DAGNode>> atoms;
        collectAtoms(expr, atoms);

        // create a new variable for each atom
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> atom_map;
        for (auto& atom : atoms) {
            std::shared_ptr<DAGNode> new_var = mkTempVar(BOOL_SORT);
            atom_map[atom] = new_var;
        }

        // use Tseitin transformation for each atom
        for(auto& atom : atoms){
            // not(atom) -> (new_var)
            clauses.emplace_back(mkOr({mkNot(atom), atom_map[atom]}));
            // (new_var) -> (atom)
            clauses.emplace_back(mkOr({mkNot(atom_map[atom]), atom}));
        }

        // create a new formula with Tseitin variables
        std::shared_ptr<DAGNode> new_expr = replaceAtoms(expr, atom_map);

        // currently, the new formula has only boolean variables
        std::shared_ptr<DAGNode> tseitin_cnf = toTseitinCNF(new_expr, clauses);
        clauses.emplace_back(tseitin_cnf);

        // if there is only one clause, return it directly
        if (clauses.size() == 1) {
            return clauses[0];
        }
        // otherwise, create an AND node, containing all OR clauses
        return mkAnd(clauses);
    }

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
    //     // eliminate xor, implies, ite
    //     expr = toNNF(expr);
    //     expr = toCNF(expr);
    //     return applyDNFDistributiveLaw(expr);
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
