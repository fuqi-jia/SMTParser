/* -*- Source -*-
*
* An SMT/OMT Parser (Operator part)
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

#include "../include/parser.h"
#include <queue>
#include <stack>

namespace SMTLIBParser{

    // mk operations
    std::shared_ptr<DAGNode> Parser::mkTrue() { return true_node; }
    std::shared_ptr<DAGNode> Parser::mkFalse() { return false_node; }
    // mk oper 
    bool isCommutative(const NODE_KIND t){
        switch(t){
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_AND:
            case NODE_KIND::NT_IAND:
            case NODE_KIND::NT_OR:
            case NODE_KIND::NT_XOR:
            case NODE_KIND::NT_BV_ADD:
            case NODE_KIND::NT_BV_MUL:
            case NODE_KIND::NT_BV_AND:
            case NODE_KIND::NT_BV_OR:
            case NODE_KIND::NT_BV_XOR:
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_DISTINCT:
                return true;
            default:
                return false;
        }
    }

    std::shared_ptr<Sort> Parser::getSort(const std::vector<std::shared_ptr<DAGNode>>& params){
        std::shared_ptr<Sort> sort = nullptr;
        for(size_t i=0;i<params.size();i++){
            if(!params[i]->isConst()){
                sort = params[i]->getSort();
                break;
            }
        }
        // all constant
        if(sort == nullptr){
            sort = params[0]->getSort();
        }
        return sort;
    }
    std::shared_ptr<Sort> Parser::getSort(std::shared_ptr<DAGNode> param){
        return param->getSort();
    }
    std::shared_ptr<Sort> Parser::getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return getSort({l, r});
    }
    std::shared_ptr<Sort> Parser::getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> m){
        return getSort({l, r, m});
    }

    std::vector<std::shared_ptr<DAGNode>> sortParams(const std::vector<std::shared_ptr<DAGNode>> &p){
        std::vector<std::shared_ptr<DAGNode>> params = p;
        std::sort(params.begin(), params.end(), [](const std::shared_ptr<DAGNode> &a, const std::shared_ptr<DAGNode> &b){
            return a->hashCode() < b->hashCode();
        });
        return params;
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p){
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(p);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(l);
        params.emplace_back(r);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(l);
        params.emplace_back(m);
        params.emplace_back(r);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p){
        if(t == NODE_KIND::NT_VAR || t == NODE_KIND::NT_CONST || t == NODE_KIND::NT_FUNC_PARAM){
            return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        }
        if(p.size() == 0) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        // make the params unique
        std::vector<std::shared_ptr<DAGNode>> params(p);
        if(isCommutative(t)){
            params = sortParams(p);
        }
        
        // check if the node is already in the node_list
        std::shared_ptr<DAGNode> newnode = std::make_shared<DAGNode>(sort, t, kindToString(t), params);
        if(complex_node_map.find(newnode)!=complex_node_map.end()){
            return node_list[complex_node_map[newnode]];
        }
        else{
            complex_node_map.insert(std::pair<std::shared_ptr<SMTLIBParser::DAGNode>, size_t>(newnode, node_list.size()));
            node_list.emplace_back(newnode);
            return newnode;
        }
    }

    // mk function
    std::shared_ptr<DAGNode> Parser::mkFuncDec(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort){
        if(fun_key_map.find(name)!=fun_key_map.end()){
            // multiple declarations
            return mkErr(ERROR_TYPE::ERR_MUL_DECL);
        }
        else{
            // create a new function
            // children: params
            // out_sort: return sort
            std::vector<std::shared_ptr<DAGNode>> children;
            for(auto &param: params){
                // TODO, a random name and not record it.
                std::shared_ptr <DAGNode> param_node = std::make_shared<DAGNode>(param, NODE_KIND::NT_FUNC_PARAM, param->toString());
                children.emplace_back(param_node);
            }
            // add a NULL_NODE to represent the function body.
            children.insert(children.begin(), NULL_NODE);

            std::shared_ptr<DAGNode> func = std::make_shared<DAGNode>(out_sort, NODE_KIND::NT_FUNC_DEC, name, children);
            fun_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, func));
            return func;
        }
    }

    std::shared_ptr<DAGNode> Parser::mkFuncDef(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body){
        std::shared_ptr<DAGNode> func = nullptr;
        if(fun_key_map.find(name)!=fun_key_map.end()){
            func = fun_key_map[name];
            assert(func->getKind() == NODE_KIND::NT_FUNC_DEC);
            // NOTE: we still check it, even if it is not necessary.
            if(func->getKind() == NODE_KIND::NT_FUNC_DEC){
                // update the function
                func = fun_key_map[name];
                func->updateFuncDef(out_sort, body, params);
                return func;
            }
            else{
                // multiple definitions
                return mkErr(ERROR_TYPE::ERR_MUL_DEF);
            }
        }
        else{
            // create a new function
            // children: params
            // out_sort: return sort
            // body: function body
            std::vector<std::shared_ptr<DAGNode>> children;
            children.emplace_back(body);
            for(auto &param: params){
                children.emplace_back(param);
            }
            std::shared_ptr<DAGNode> func = std::make_shared<DAGNode>(out_sort, NODE_KIND::NT_FUNC_DEF, name, children);
            fun_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, func));
            return func;
        }
    }


    std::shared_ptr<Sort> Parser::mkSortDec(const std::string &name, const size_t &arity){
        if(sort_key_map.find(name)!=sort_key_map.end()){
            // multiple declarations
            err_mul_decl(name, line_number);
            return NULL_SORT;
        }
        else{
            std::shared_ptr<Sort> sort = std::make_shared<Sort>(SORT_KIND::SK_DEC, name, arity);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(name, sort));
            return sort;
        }
    }


    // CORE OPERATORS
    /*
    (= A A+ :chainable), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
        if(l->isTrue() && r->isTrue()){
            return mkTrue();
        }
        else if(l->isFalse() && r->isFalse()){
            return mkTrue();
        }
        else if(l->isTrue() && r->isFalse()){
            return mkFalse();
        }
        else if(l->isFalse() && r->isTrue()){
            return mkFalse();
        }
        else if(l->isTrue()){
            return r;
        }
        else if(l->isFalse()){
            return mkNot(r);
        }
        else if(r->isTrue()){
            return l;
        }
        else if(r->isFalse()){
            return mkNot(l);
        }
        else if(l->isNot() && r->isNot()){
            // reduce nested not
            assert(l->getChildrenSize() == 1);
            assert(r->getChildrenSize() == 1);
            return mkEq(l->getChild(0), r->getChild(0));
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_EQ, l, r);
        }
    }
    std::shared_ptr<DAGNode> Parser::mkEq(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkEq(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            if(params[i]->isTrue()){
                // x = true => x
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all true constant
            return mkTrue();
        }
        else if(new_params.size() == 1){
            // only one uncertain param
            return new_params[0];
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_EQ, new_params);
        }
    }
    /*
    (distinct A A+ :std::pairwise), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkDistinct(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isTrue() && r->isTrue()){
            return mkFalse();
        }
        else if(l->isFalse() && r->isFalse()){
            return mkFalse();
        }
        else if(l->isTrue() && r->isFalse()){
            return mkTrue();
        }
        else if(l->isFalse() && r->isTrue()){
            return mkTrue();
        }
        else if(l->isTrue()){
            return mkNot(r);
        }
        else if(l->isFalse()){
            return r;
        }
        else if(r->isTrue()){
            return mkNot(l);
        }
        else if(r->isFalse()){
            return l;
        }
        else if(l->isNot() && r->isNot()){
            // reduce nested not
            assert(l->getChildrenSize() == 1);
            assert(r->getChildrenSize() == 1);
            return mkDistinct(l->getChild(0), r->getChild(0));
        }
        else if(l->isNot()){
            return mkDistinct(l->getChild(0), r);
        }
        else if(r->isNot()){
            return mkDistinct(l, r->getChild(0));
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_DISTINCT, l, r);
        }
    }
    std::shared_ptr<DAGNode> Parser::mkDistinct(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            if(params[i]->isFalse()){
                // x != False => x
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all false constant
            return mkFalse();
        }
        else if(new_params.size() == 1){
            // only one uncertain param
            return new_params[0];
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_DISTINCT, new_params);
        }
    }
    // CONST
    std::shared_ptr<DAGNode>	Parser::mkConst(const std::shared_ptr<Sort>& sort, const std::string &v){
        if(constants.find(v)!=constants.end()){
            return node_list[constants[v]];
        }
        else{
            std::shared_ptr<DAGNode> newconst = std::make_shared<DAGNode>(sort, NODE_KIND::NT_CONST, v);
            constants.insert(std::pair<std::string, size_t>(v, node_list.size()));
            node_list.emplace_back(newconst);
            return newconst;
        }
    }
    std::shared_ptr<DAGNode> Parser::mkConstBool(const std::string &v){
        return mkConst(BOOL_SORT, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstInt(const Integer &v){
        return mkConst(INTOREAL_SORT, toString(v));
    }
    std::shared_ptr<DAGNode> Parser::mkConstInt(const std::string &v){
        return mkConst(INTOREAL_SORT, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstRat(const Rational &v){
        return mkConst(RAT_SORT, v.get_str());
    }
    std::shared_ptr<DAGNode> Parser::mkConstRat(const Rational &l, const Rational &r){
        Rational v = l/r;
        return mkConst(RAT_SORT, v.get_str()); 
    }
    std::shared_ptr<DAGNode> Parser::mkConstRat(const Integer &l, const Integer &r){
        Rational v = Rational(l)/Rational(r);
        return mkConst(RAT_SORT, v.get_str());
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const std::string &v){
        return mkConst(REAL_SORT, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const Real &v){
        return mkConst(REAL_SORT, toString(v));
    }
    std::shared_ptr<DAGNode> Parser::mkConstStr(const std::string &v){
        return mkConst(STR_SORT, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstBv(const std::string &v, const size_t& width){
        std::string sort_key_name = "BV_" + std::to_string(width);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = mkBVSort(width);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkConst(sort, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstFp(const std::string &v, const size_t& e, const size_t& s){
        std::string sort_key_name = "FP_" + std::to_string(e) + "_" + std::to_string(s);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = mkFPSort(e, s);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkConst(sort, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReg(const std::string &v){
        return mkConst(REG_SORT, v);
    }
    
    // VAR
    std::shared_ptr<DAGNode> Parser::mkVar(const std::shared_ptr<Sort>& sort, const std::string &name){
        if(var_names.find(name)!=var_names.end()){
            // multiple declarations
            return node_list[var_names[name]];
        }
        else{
            std::shared_ptr<DAGNode> newvar = std::make_shared<DAGNode>(sort, NODE_KIND::NT_VAR, name);
            var_names.insert(std::pair<std::string, size_t>(name, node_list.size()));
            node_list.emplace_back(newvar);
            return newvar;
        }
    }
    std::shared_ptr<DAGNode> Parser::mkVarBool(const std::string &name){
        return mkVar(BOOL_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarInt(const std::string &name){
        return mkVar(INT_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarReal(const std::string &name){
        return mkVar(REAL_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarBv(const std::string &name, const size_t& width){
        std::string sort_key_name = "BV_" + std::to_string(width);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = mkBVSort(width);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkVar(sort, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarFp(const std::string &name, const size_t& e, const size_t& s){
        std::string sort_key_name = "FP_" + std::to_string(e) + "_" + std::to_string(s);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = mkFPSort(e, s);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkVar(sort, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarStr(const std::string &name){
        return mkVar(STR_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarReg(const std::string &name){
        return mkVar(REG_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkFunParamVar(std::shared_ptr<Sort> sort, const std::string &name){
        std::shared_ptr<DAGNode> newvar = std::make_shared<DAGNode>(sort, NODE_KIND::NT_FUNC_PARAM, name);
        // do not insert into variables
        // it is a function parameter
        return newvar;
    }
    // ARRAY
    std::shared_ptr<DAGNode> Parser::mkArray(const std::string &name, std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem){
        std::string sort_key_name = "ARRAY_" + index->toString() + "_" + elem->toString();
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = mkArraySort(index, elem);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkVar(sort, name);
    }
    // BOOLEAN
    /*
    (not Bool), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkNot(std::shared_ptr<DAGNode> param){
        
        if (param->isErr())	return param;

        if (param->isNot()) {
            // reduce nested not
            assert(param->getChildrenSize() == 1);
            return param->getChild(0);
        }
        else if(param->isTrue()){
            return mkFalse();
        }
        else if(param->isFalse()){
            return mkTrue();
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_NOT, param);
        }
    }
    /*
    (and Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkAnd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        else if(params.size() == 1) return params[0];

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for (size_t i = 0; i < params.size(); i++) {

            if (params[i]->isErr()) {
                return params[i];
            }
            else if(params[i]->isTrue()){
                // true constant
                continue;
            }
            else if(params[i]->isFalse()){
                // false constant
                return mkFalse();
            }
            else {
                // insert uncertain param
                new_params.emplace_back(params[i]);
            }
        }

        if (new_params.size() == 0) {
            // all true constant
            return mkTrue();
        }
        else if (new_params.size() == 1) {
            // only one uncertain param
            return new_params[0];
        }
        else {
            // make new AND operator
            return mkOper(BOOL_SORT, NODE_KIND::NT_AND, new_params);
        }
    }
    /*
    (or Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkOr(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        else if(params.size() == 1) return params[0];

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for (size_t i = 0; i < params.size(); i++) {

            if (params[i]->isErr()) {
                return params[i];
            }
            else if(params[i]->isFalse()){
                // false constant
                continue;
            }
            else if(params[i]->isTrue()){
                // true constant
                return mkTrue();
            }
            else {
                // insert uncertain param
                new_params.emplace_back(params[i]);
            }
        }

        if (new_params.size() == 0) {
            // all false constant
            return mkFalse();
        }
        else if (new_params.size() == 1) {
            // only one uncertain param
            return new_params[0];
        }
        else {
            // make new OR operator
            return mkOper(BOOL_SORT, NODE_KIND::NT_OR, new_params);
        }
    }
    /*
    (=> Bool Bool+ :right-assoc), return Bool
    (=> a b c d) <=> (or -a -b -c d)
    */
    std::shared_ptr<DAGNode> Parser::mkImplies(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);

        std::vector<std::shared_ptr<DAGNode>> new_params;
        // (=> a b c d) <=> (or -a -b -c d)
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(params[i]->isFalse()){
                // -params[i] => true
                return mkTrue();
            }
            else if(params[i]->isTrue()){
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(params.back()->isErr()) return params.back();

        if(new_params.size() == 0){
            // all true constant
            // true -> params.back() => params.back()
            return params.back();
        }

        new_params.emplace_back(params.back());

        return mkOper(BOOL_SORT, NODE_KIND::NT_IMPLIES, new_params);

        // do not transform
        // // transform imply into or
        // // (=> a b c d) <=> (or -a -b -c d)
        // for (size_t i = 0; i < new_params.size() - 1; i++) {
        //     new_params[i] = mkNot(new_params[i]);
        //     if(new_params[i]->isErr()) return new_params[i];
        // }

        // if(new_params.back()->isErr()) return new_params.back();
        // return mkOr(new_params);
    }
    /*
    (xor Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkXor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);

        std::vector<std::shared_ptr<DAGNode>> new_params;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(params[i]->isFalse()){
                // x xor false = x
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all false constant
            return mkFalse();
        }
        else if(new_params.size() == 1){
            // only one uncertain param
            return new_params[0];
        }
        else{
            return mkOper(BOOL_SORT, NODE_KIND::NT_XOR, new_params);
        }
    }
    /*
    (ite Bool A A), return A
    */
    std::shared_ptr<DAGNode> Parser::mkIte(std::shared_ptr<DAGNode> cond, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(cond->isErr()) return cond;
        if(l->isErr()) return l;
        if(r->isErr()) return r;

        if(cond->isTrue()){
            return l;
        }
        else if(cond->isFalse()){
            return r;
        }
        else{
            return mkOper(l->getSort(), NODE_KIND::NT_ITE, cond, l, r);
        }
    }
    std::shared_ptr<DAGNode> Parser::mkIte(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);

        return mkIte(params[0], params[1], params[2]);
    }
    // ARITHMATIC COMMON OPERATORS
    /*
    (+ rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        if(params.size() == 1){
            return params[0];
        }
        assert(params.size() >= 2);
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        Integer IntSum = 0;
        Real RealSum = 0.0;
        Rational RatSum = 0;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            if(params[i]->isCInt()){
                IntSum += params[i]->toInt();
            }
            else if(params[i]->isCReal()){
                RealSum += params[i]->toReal();
            }
            else if(params[i]->isCRat()){
                RatSum += params[i]->toRat();
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all 0 constant
            if(sort->isInt()){
                return mkConstInt(IntSum);
            }
            else if(sort->isReal()){
                return mkConstReal(RealSum);
            }
            else if(sort->isRat()){
                return mkConstRat(RatSum);
            }
            else{
                return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            }
        }
        else if(new_params.size() == 1 && (IntSum == 0 && RealSum == 0.0)){
            // only one uncertain param
            return new_params[0];
        }
        else{
            if(sort->isInt()){
                new_params.emplace_back(mkConstInt(IntSum));
            }
            else if(sort->isReal()){
                if(IntSum != 0) new_params.emplace_back(mkConstInt(IntSum));
                if(RealSum != 0.0) new_params.emplace_back(mkConstReal(RealSum));
                if(RatSum != 0) new_params.emplace_back(mkConstRat(RatSum));
            }
            else if(sort->isRat()){
                if(RatSum != 0) new_params.emplace_back(mkConstRat(RatSum));
                if(IntSum != 0) new_params.emplace_back(mkConstInt(IntSum));
            }
            return mkOper(sort, NODE_KIND::NT_ADD, new_params);
        }
    }
    /*
    (* rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 1){
            return params[0];
        }
        assert(params.size() >= 2);
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        Integer IntProd = 1;
        Real RealProd = 1.0;
        Rational RatProd = 1;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            if(params[i]->isCInt()){
                IntProd *= params[i]->toInt();
            }
            else if(params[i]->isCReal()){
                RealProd *= params[i]->toReal();
            }
            else if(params[i]->isCRat()){
                RatProd *= params[i]->toRat();
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all 1 constant
            if(sort->isInt()){
                return mkConstInt(IntProd);
            }
            else if(sort->isReal()){
                return mkConstReal(RealProd);
            }
            else if(sort->isRat()){
                return mkConstRat(RatProd);
            }
            else{
                return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            }
        }
        else if(new_params.size() == 1 && (IntProd == 1 && RealProd == 1.0)){
            // only one uncertain param
            return new_params[0];
        }
        else{
            if(sort->isInt()){
                if(IntProd == 0) return mkConstInt("0");
                else if(IntProd != 1){
                    new_params.emplace_back(mkConstInt(IntProd));
                }
            }
            else if(sort->isReal()){
                if(IntProd == 0) return mkConstInt("0");
                else if(IntProd != 1){
                    new_params.emplace_back(mkConstInt(IntProd));
                }

                if(RealProd == 0.0) return mkConstReal("0");
                else if(RealProd != 1.0){
                    new_params.emplace_back(mkConstReal(RealProd));
                }

                if(RatProd == 0) return mkConstReal("0");
                else if(RatProd != 1){
                    new_params.emplace_back(mkConstRat(RatProd));
                }
            }
            else if(sort->isRat()){
                if(IntProd == 0) return mkConstReal("0");
                else if(IntProd != 1){
                    new_params.emplace_back(mkConstInt(IntProd));
                }

                if(RatProd == 0) return mkConstReal("0");
                else if(RatProd != 1){
                    new_params.emplace_back(mkConstRat(RatProd));
                }
            }
            return mkOper(sort, NODE_KIND::NT_MUL, new_params);
        }
    }

    /*
    (iand rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkIand(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 1){
            return params[0];
        }
        assert(params.size() >= 2);
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_IAND, new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkPow2(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstInt(pow(2, param->toInt()));
        }
        return mkOper(param->getSort(), NODE_KIND::NT_POW2, param);
    }
    std::shared_ptr<DAGNode> Parser::mkPow(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstInt(pow(l->toInt(), r->toInt()));
        }

        return mkOper(l->getSort(), NODE_KIND::NT_POW, l, r);
    }
    /*
    (- rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        if(params.size() == 1){
            return mkNeg(params[0]);
        }
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;
        // (- a b c)
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort()->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_SUB, new_params);
    }
    /*
    (- rt), return rt
    */  
    std::shared_ptr<DAGNode> Parser::mkNeg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstInt(-param->toInt());
        }
        else if(param->isCReal()){
            return mkConstReal(-param->toReal());
        }
        return mkOper(param->getSort(), NODE_KIND::NT_NEG, param);
    }
    /*
    (div Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkDivInt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstInt(l->toInt() / r->toInt());
        }
        return mkOper(INT_SORT, NODE_KIND::NT_DIV_INT, l, r);
    }
    /*
    (/ Real Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkDivReal(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstRat(l->toInt(), r->toInt());
        }

        return mkOper(REAL_SORT, NODE_KIND::NT_DIV_REAL, l, r);
    }
    /*
    (mod Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkMod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstInt(l->toInt() % r->toInt());
        }

        return mkOper(INT_SORT, NODE_KIND::NT_MOD, l, r);
    }
    /*
    (abs Int), return Int
    (abs Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAbs(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstInt(abs(param->toInt()));
        }
        else if(param->isCReal()){
            return mkConstReal(abs(param->toReal()));
        }
        return mkOper(param->getSort(), NODE_KIND::NT_ABS, param);
    }
    /*
    (sqrt Real), return Real
    (sqrt Int), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSqrt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstReal(sqrt(param->toInt()));
        }
        else if(param->isCReal()){
            return mkConstReal(sqrt(param->toReal()));
        }
        return mkOper(REAL_SORT, NODE_KIND::NT_SQRT, param);
    }
    /*
    (ceil Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkCeil(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return param;
        }
        else if(param->isCReal()){
            return mkConstInt(ceil(param->toReal()));
        }
        return mkOper(INT_SORT, NODE_KIND::NT_CEIL, param);
    }
    /*
    (floor Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkFloor(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return param;
        }
        else if(param->isCReal()){
            return mkConstInt(floor(param->toReal()));
        }
        return mkOper(INT_SORT, NODE_KIND::NT_FLOOR, param);

    }
    /*
    (round Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkRound(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return param;
        }
        else if(param->isCReal()){
            return mkConstInt(round(param->toReal()));
        }
        return mkOper(INT_SORT, NODE_KIND::NT_ROUND, param);
    }
    // TRANSCENDENTAL ARITHMATIC
    /*
    (exp Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkExp(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            if(param->toInt() == 0){
                return mkConstReal(1.0);
            }
            else if(param->toInt() == 1){
                return mkE();
            }
        }
        else if(param->isCReal()){
            if(param->toReal() == 0.0){
                return mkConstReal(1.0);
            }
            else if(param->toReal() == 1.0){
                return mkE();
            }
        }
        return mkOper(REAL_SORT, NODE_KIND::NT_EXP, param);
    }
    /*
    (ln Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLn(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            if(param->toInt() <= 0){
                return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
            }
            else if(param->toInt() == 1){
                return mkConstReal(0.0);
            }
        }
        else if(param->isCReal()){
            if(param->toReal() <= 0.0){
                return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
            }
            else if(param->toReal() == 1.0){
                return mkConstReal(0.0);
            }
            else if(param->isE()){
                return mkConstReal(1.0);
            }
        }
        return mkOper(REAL_SORT, NODE_KIND::NT_LN, param);
    }
    /*
    (lg Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            if(param->toInt() <= 0){
                return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
            }
            else if(param->toInt() == 1){
                return mkConstReal(0.0);
            }
            else if(param->toInt() == 10){
                return mkConstReal(1.0);
            }
            else if(param->toInt() == 100){
                return mkConstReal(2.0);
            }
            else if(param->toInt() == 1000){
                return mkConstReal(3.0);
            }
            else if(param->toInt() == 10000){
                return mkConstReal(4.0);
            }
            else if(param->toInt() == 100000){
                return mkConstReal(5.0);
            }
            else if(param->toInt() == 1000000){
                return mkConstReal(6.0);
            }
            else if(param->toInt() == 10000000){
                return mkConstReal(7.0);
            }
            else if(param->toInt() == 100000000){
                return mkConstReal(8.0);
            }
            else if(param->toInt() == 1000000000){
                return mkConstReal(9.0);
            }
            else if(param->toInt() == 10000000000){
                return mkConstReal(10.0);
            }
            // ... ...
        }
        else if(param->isCReal()){
            if(param->toReal() <= 0.0){
                return mkErr(ERROR_TYPE::ERR_NEG_PARAM);
            }
            else if(param->toReal() == 1.0){
                return mkConstReal(0.0);
            }
            else if(param->toReal() == 10.0){
                return mkConstReal(1.0);
            }
            else if(param->toReal() == 100.0){
                return mkConstReal(2.0);
            }
            else if(param->toReal() == 1000.0){
                return mkConstReal(3.0);
            }
            else if(param->toReal() == 10000.0){
                return mkConstReal(4.0);
            }
            else if(param->toReal() == 100000.0){
                return mkConstReal(5.0);
            }
            else if(param->toReal() == 1000000.0){
                return mkConstReal(6.0);
            }
            else if(param->toReal() == 10000000.0){
                return mkConstReal(7.0);
            }
            else if(param->toReal() == 100000000.0){
                return mkConstReal(8.0);
            }
            else if(param->toReal() == 1000000000.0){
                return mkConstReal(9.0);
            }
            else if(param->toReal() == 10000000000.0){
                return mkConstReal(10.0);
            }
            // ... ...
        }
        return mkOper(REAL_SORT, NODE_KIND::NT_LG, param);
    }
    /*
    (log Real Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLog(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            if(l->toInt() <= 0 || r->toInt() <= 0){
                return l->isErr()?l:r;
            }
            else if(l->toInt() == 1){
                return l->isErr()?l:r;
            }
            else if(r->toInt() == 1){
                return mkConstReal(0.0);
            }
        }
        else if(l->isCReal() && r->isCReal()){
            if(l->toReal() <= 0.0 || r->toReal() <= 0.0){
                return l->isErr()?l:r;
            }
            else if(l->toReal() == 1.0){
                return l->isErr()?l:r;
            }
            else if(r->toReal() == 1.0){
                return mkConstReal(0.0);
            }
        }

        return mkOper(REAL_SORT, NODE_KIND::NT_LOG, l, r);
    }
    /*
    (sin Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSin(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_SIN, param);
    }
    /*
    (cos Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCos(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_COS, param);
    }
    /*
    (sec Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSec(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_SEC, param);
    }
    /*
    (csc Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCsc(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_CSC, param);
    }
    /*
    (tan Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkTan(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_TAN, param);
    }
    /*
    (cot Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCot(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_COT, param);
    }
    /*
    (asin Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsin(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ASIN, param);
    }
    /*
    (acos Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcos(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACOS, param);
    }
    /*
    (asec Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsec(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ASEC, param);
    }
    /*
    (acsc Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcsc(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACSC, param);
    }
    /*
    (atan Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAtan(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ATAN, param);
    }
    /*
    (acot Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcot(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACOT, param);
    }
    /*
    (sinh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSinh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_SINH, param);
    }
    /*
    (cosh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCosh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_COSH, param);
    }
    /*
    (tanh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkTanh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_TANH, param);
    }
    /*
    (sech Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSech(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_SECH, param);
    }
    /*
    (csch Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCsch(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_CSCH, param);
    }
    /*
    (coth Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCoth(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_COTH, param);
    }
    /*
    (asinh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsinh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ASINH, param);
    }
    /*
    (acosh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcosh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACOSH, param);
    }
    /*
    (atanh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAtanh(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ATANH, param);
    }
    /*
    (asech Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsech(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ASECH, param);
    }
    /*
    (acsch Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcsch(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACSCH, param);
    }
    /*
    (acoth Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcoth(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(REAL_SORT, NODE_KIND::NT_ACOTH, param);
    }
    // ARITHMATIC COMP
    /*
    (<= rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return l->toInt() <= r->toInt() ? mkTrue() : mkFalse();
        }
        else if(l->isCReal() && r->isCReal()){
            return l->toReal() <= r->toReal() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_LE, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return l->toInt() < r->toInt() ? mkTrue() : mkFalse();
        }
        else if(l->isCReal() && r->isCReal()){
            return l->toReal() < r->toReal() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_LT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return l->toInt() >= r->toInt() ? mkTrue() : mkFalse();
        }
        else if(l->isCReal() && r->isCReal()){
            return l->toReal() >= r->toReal() ? mkTrue() : mkFalse();
        }
        return mkOper(BOOL_SORT, NODE_KIND::NT_GE, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return l->toInt() > r->toInt() ? mkTrue() : mkFalse();
        }
        else if(l->isCReal() && r->isCReal()){
            return l->toReal() > r->toReal() ? mkTrue() : mkFalse();
        }
        return mkOper(BOOL_SORT, NODE_KIND::NT_GT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkLe(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkLe(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (<= a b c d) <=> (and (<= a b) (<= b c) (<= c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            std::shared_ptr<DAGNode> le = mkLe(params[i], params[i + 1]);
            if(le->isErr()) return le;
            new_params.emplace_back(le);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkLt(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkLt(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (< a b c d) <=> (and (< a b) (< b c) (< c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            std::shared_ptr<DAGNode> lt = mkLt(params[i], params[i + 1]);
            if(lt->isErr()) return lt;
            new_params.emplace_back(lt);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkGe(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkGe(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (>= a b c d) <=> (and (>= a b) (>= b c) (>= c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            std::shared_ptr<DAGNode> ge = mkGe(params[i], params[i + 1]);
            if(ge->isErr()) return ge;
            new_params.emplace_back(ge);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkGt(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkGt(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (> a b c d) <=> (and (> a b) (> b c) (> c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            std::shared_ptr<DAGNode> gt = mkGt(params[i], params[i + 1]);
            if(gt->isErr()) return gt;
            new_params.emplace_back(gt);
        }

        return mkAnd(new_params);
    }
    // ARITHMATIC CONVERSION
    /*
    (to_int Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkToInt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return param;
        }
        else if(param->isCReal()){
            return mkConstInt((Integer)param->toReal());
        }
        return mkOper(INT_SORT, NODE_KIND::NT_TO_INT, param);
    }
    /*
    (to_real Int), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkToReal(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstReal((Real)param->toInt());
        }
        else if(param->isCReal()){
            return param;
        }
        return mkOper(REAL_SORT, NODE_KIND::NT_TO_REAL, param);
    }
    // ARITHMATIC PROPERTIES
    /*
    (is_int Real), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsInt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        return mkOper(BOOL_SORT, NODE_KIND::NT_IS_INT, param);
    }
    /*
    (is_divisible Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsDivisible(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return l->toInt() % r->toInt() == 0 ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_IS_DIVISIBLE, l, r);
    }
    /*
    (is_prime Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsPrime(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            if(isPrime(param->toInt())){
                return mkTrue();
            }
            else{
                return mkFalse();
            }
        }
        return mkOper(BOOL_SORT, NODE_KIND::NT_IS_PRIME, param);
    }
    /*
    (is_even Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsEven(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return isEven(param->toInt()) ? mkTrue() : mkFalse();
        }
        return mkOper(BOOL_SORT, NODE_KIND::NT_IS_EVEN, param);
    }
    /*
    (is_odd Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsOdd(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return isOdd(param->toInt()) ? mkTrue() : mkFalse();
        }
        return mkOper(BOOL_SORT, NODE_KIND::NT_IS_ODD, param);
    }
    // ARITHMATIC CONSTANTS
    std::shared_ptr<DAGNode> Parser::mkPi(){
        return mkConst(REAL_SORT, "PI");
    }
    std::shared_ptr<DAGNode> Parser::mkE(){
        return mkConst(REAL_SORT, "E");
    }
    std::shared_ptr<DAGNode> Parser::mkInfinity(){
        return mkConst(EXT_SORT, "INF");
    }
    std::shared_ptr<DAGNode> Parser::mkNan(){
        return mkConst(EXT_SORT, "NaN");
    }
    std::shared_ptr<DAGNode> Parser::mkEpsilon(){
        return mkConst(EXT_SORT, "EPSILON");
    }
    // ARITHMATIC FUNCTIONS
    // /*
    // (sum rt rt+), return rt
    // */
    // std::shared_ptr<DAGNode> Parser::mkSum(const std::vector<std::shared_ptr<DAGNode>> &params); // \Sum params
    // std::shared_ptr<DAGNode> Parser::mkProd(const std::vector<std::shared_ptr<DAGNode>> &params); // \Prod params
    /*
    (gcd Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkGcd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstInt(gcd(l->toInt(), r->toInt()));
        }

        return mkOper(INT_SORT, NODE_KIND::NT_GCD, l, r);
    }
    /*
    (lcm Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkLcm(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCInt() && r->isCInt()){
            return mkConstInt(lcm(l->toInt(), r->toInt()));
        }

        return mkOper(INT_SORT, NODE_KIND::NT_LCM, l, r);
    }
    /*
    (factorial Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkFact(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCInt()){
            return mkConstInt(factorial(param->toInt()));
        }
        return mkOper(INT_SORT, NODE_KIND::NT_FACT, param);
    }
    // BITVECTOR COMMON OPERATORS
    /*
    (bv_not Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNot(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCBV()){
            return mkConstBv(bvNot(param->toString()), param->getSort()->getBitWidth());
        }
        return mkOper(param->getSort(), NODE_KIND::NT_NOT, param);
    }
    /*
    (bvand Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvAnd(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_AND, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvAnd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvAnd(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkAnd(new_params);
    }
    /*
    (bvor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvOr(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_OR, l, r);
    }
    /*
    (bvor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvOr(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvOr(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_OR, new_params);

    }
    std::shared_ptr<DAGNode> Parser::mkBvXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvXor(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_XOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvXor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvXor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_XOR, new_params);
    }
    /*
    (bvnand Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNand(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvNand(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_NAND, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvNand(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvNand(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_NAND, new_params);
    }
    /*
    (bvnor Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvNor(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_NOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvNor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvNor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_NOR, new_params);
    }
    /*
    (bvxnor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvXnor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvXnor(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_XNOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvXnor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvXnor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_XNOR, new_params);
    }
    /*
    (bvcomp Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvComp(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_COMP) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_COMP, l, r);
    }
    /*
    (bvneg Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNeg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(param->isCBV()){
            return mkConstBv(bvNeg(param->toString()), param->getSort()->getBitWidth());
        }
        return mkOper(param->getSort(), NODE_KIND::NT_BV_NEG, param);
    }
    /*
    (bvadd Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvAdd(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_ADD, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvAdd(params[0], params[1]);
        }

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_ADD, new_params);
    }
    /*
    (bvsub Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvSub(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_SUB, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvSub(params[0], params[1]);
        }

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_SUB, new_params);
    }
    /*
    (bvmul Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvMul(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_MUL, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvMul(params[0], params[1]);
        }

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_BV_MUL, new_params);
    }
    /*
    (bvudiv Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvUdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvUdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_UDIV, l, r);
    }
    /*
    (bvurem Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvUrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvUrem(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_UREM, l, r);
    }
    /*
    (bvsdiv Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvSdiv(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_SDIV, l, r);
    }
    /*
    (bvsrem Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvSrem(l->toString(), r->toString()), r->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_SREM, l, r);
    }
    /*
    (bvsmod Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvSmod(l->toString(), r->toString()), r->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_SMOD, l, r);
    }
    /*
    (bvshl Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvShl(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvShl(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }


        return mkOper(l->getSort(), NODE_KIND::NT_BV_SHL, l, r);
    }
    /*
    (bvlshr Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvLshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvLshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_LSHR, l, r);
    }
    /*
    (bvashr Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvAshr(l->toString(), r->toString()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_ASHR, l, r);
    }
    /*
    (bvconcat Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        size_t width = 0;
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            width += params[i]->getSort()->getBitWidth();
            new_params.emplace_back(params[i]);
        }

        std::shared_ptr<Sort> new_sort = mkBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_CONCAT, new_params);
    }
    /*
    (bvextract Bv Int Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvExtract(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt() || !s->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV() && s->isCBV()){
            Integer size = (s->toInt() - r->toInt());
            return mkConstBv(bvExtract(l->toString(), r->toInt(), s->toInt()), size.get_ui());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_EXTRACT, l, r, s);
    }
    /*
    (bvrepeat Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            Integer size = l->getSort()->getBitWidth() * r->toInt();
            return mkConstBv(bvRepeat(l->toString(), r->toInt()), size.get_ui());
        }

        size_t width = l->getSort()->getBitWidth() * r->toInt().get_ui();
        std::shared_ptr<Sort> new_sort = mkBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_REPEAT, l, r);
    }
    /*
    (zero_extend Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvZeroExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            Integer size = l->getSort()->getBitWidth() + r->toInt();
            return mkConstBv(bvZeroExtend(l->toString(), r->toInt()), size.get_ui());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_ZERO_EXT, l, r);
    }
    /*
    (bvsign_extend Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSignExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            Integer size = l->getSort()->getBitWidth() + r->toInt();
            return mkConstBv(bvSignExtend(l->toString(), r->toInt()), size.get_ui());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_SIGN_EXT, l, r);
    }
    /*
    (bvrotate_left Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRotateLeft(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvRotateLeft(l->toString(), r->toInt()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_ROTATE_LEFT, l, r);
    }
    /*
    (bvrotate_right Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRotateRight(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return mkConstBv(bvRotateRight(l->toString(), r->toInt()), l->getSort()->getBitWidth());
        }

        return mkOper(l->getSort(), NODE_KIND::NT_BV_ROTATE_RIGHT, l, r);
    }
    // BITVECTOR COMP
    /*
    (bvult Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_ULT) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_ULT, l, r);
    }
    /*
    (bvule Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_ULE) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_ULE, l, r);
    }
    /*
    (bvugt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_UGT) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_UGT, l, r);
    }
    /*
    (bvuge Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_UGE) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_UGE, l, r);
    }
    /*
    (bvslt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SLT) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_SLT, l, r);
    }
    /*
    (bvsle Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SLE) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_SLE, l, r);
    }
    /*
    (bvsgt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SGT) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_SGT, l, r);
    }
    /*
    (bvsge Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isBv() || r->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCBV() && r->isCBV()){
            return bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SGE) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_BV_SGE, l, r);
    }
    // BITVECTOR CONVERSION
    /*
    (bv2nat Bv), return Nat
    */
    std::shared_ptr<DAGNode> Parser::mkBvToNat(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV()){
            return mkConstInt(bvToNat(param->toString()));
        }

        return mkOper(NAT_SORT, NODE_KIND::NT_BV_TO_NAT, param);
    }
    /*
    (nat2bv Nat Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkNatToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        if(param->isErr() || size->isErr()) return param->isErr()?param:size;
        if(!param->getSort()->isInt() || !size->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(natToBv(param->toInt(), size->toInt()), size->toInt().get_ui());
        }

        std::shared_ptr<Sort> new_sort = mkBVSort(size->toInt().get_ui());

        return mkOper(new_sort, NODE_KIND::NT_NAT_TO_BV, param, size);
    }
    /*
    (bv2int Bv), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkBvToInt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isBv()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV()){
            return mkConstInt(bvToInt(param->toString()));
        }

        return mkOper(INT_SORT, NODE_KIND::NT_BV_TO_INT, param);
    }
    /*
    (int2bv Int Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkIntToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        if(param->isErr() || size->isErr()) return param->isErr()?param:size;
        if(!param->getSort()->isInt() || !size->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(intToBv(param->toInt(), size->toInt()), size->toInt().get_ui());
        }

        std::shared_ptr<Sort> new_sort = mkBVSort(size->toInt().get_ui());

        return mkOper(new_sort, NODE_KIND::NT_INT_TO_BV, param, size);
    }

    // FLOATING POINT COMMON OPERATORS
    /*
    (fp.add Fp Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_ADD, new_params);
    }
    /*
    (fp.sub Fp Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_SUB, new_params);
    }
    /*
    (fp.mul Fp Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_MUL, new_params);
    }
    /*
    (fp.div Fp Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpDiv(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_DIV, new_params);
    }
    /*
    (fp.abs Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpAbs(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(param->getSort(), NODE_KIND::NT_FP_ABS, param);
    }
    /*
    (fp.neg Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpNeg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(param->getSort(), NODE_KIND::NT_FP_NEG, param);
    }
    /*
    (fp.rem Fp Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpRem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(l->getSort()->isFp() || r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(l->getSort(), NODE_KIND::NT_FP_REM, l, r);
    }
    /*
    (fp.fma Fp Fp Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpFma(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 3) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 2;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_FMA, new_params);
    }
    /*
    (fp.sqrt Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpSqrt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(param->getSort(), NODE_KIND::NT_FP_SQRT, param);
    }
    /*
    (fp.roundToIntegral Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpRoundToIntegral(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(param->getSort(), NODE_KIND::NT_FP_ROUND_TO_INTEGRAL, param);
    }
    /*
    (fp.min Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpMin(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_MIN, new_params);
    }
    /*
    (fp.max Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpMax(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort() ->isEqTo(sort)) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_FP_MAX, new_params);
    }
    // FLOATING POINT COMP
    /*
    (fp.leq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isFp() || !r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_LE, l, r);
    }
    /*
    (fp.lt Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isFp() || !r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_LT, l, r);
    }
    /*
    (fp.geq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isFp() || !r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_GE, l, r);
    }
    /*
    (fp.gt Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isFp() || !r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_GT, l, r);
    }
    /*
    (fp.eq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isFp() || !r->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_EQ, l, r);
    }
    // FLOATING POINT CONVERSION
    /*
    (fp.to_ubv Fp), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkFpToUbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        if(param->isErr() || size->isErr()) return param->isErr()?param:size;
        if(!param->getSort()->isFp() || !size->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(fpToUbv(param->toString(), size->toInt()), size->toInt().get_ui());
        }

        std::shared_ptr<Sort> new_sort = mkBVSort(size->toInt().get_ui());

        return mkOper(new_sort, NODE_KIND::NT_FP_TO_UBV, param, size);
    }
    std::shared_ptr<DAGNode> Parser::mkFpToSbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        if(param->isErr() || size->isErr()) return param->isErr()?param:size;
        if(!param->getSort()->isFp() || !size->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(fpToSbv(param->toString(), size->toInt()), size->toInt().get_ui());
        }

        std::shared_ptr<Sort> new_sort = mkBVSort(size->toInt().get_ui());

        return mkOper(new_sort, NODE_KIND::NT_FP_TO_SBV, param, size);
    }
    std::shared_ptr<DAGNode> Parser::mkFpToReal(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REAL_SORT, NODE_KIND::NT_FP_TO_REAL, param);
    }
    /*
    (to_fp Bv Bv Bv), return Fp
    (to_fp Real Real Real), return Fp
    ...
    */
    std::shared_ptr<DAGNode> Parser::mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> param){
        if(eb->isErr() || sb->isErr() || param->isErr()) return eb->isErr()?eb:(sb->isErr()?sb:param);

        std::shared_ptr<Sort> sort = mkFPSort(eb->toInt().get_ui(), sb->toInt().get_ui());

        return mkOper(sort, NODE_KIND::NT_FP_TO_FP, eb, sb, param);
    }
    // FLOATING POINT PROPERTIES
    /*
    (fp.isNormal Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNormal(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_NORMAL, param);
    }
    /*
    (fp.isSubnormal Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsSubnormal(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_SUBNORMAL, param);
    }
    /*
    (fp.isZero Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsZero(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_ZERO, param);
    }
    /*
    (fp.isInfinite Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsInf(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_INF, param);
    }
    /*
    (fp.isNaN Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNan(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_NAN, param);
    }
    /*
    (fp.isNegative Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNeg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_NEG, param);
    }
    /*
    (fp.isPositive Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsPos(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isFp()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_FP_IS_POS, param);
    }
    // ARRAY
    /*
    (select Array Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkSelect(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isArray() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(l->getSort()->getElemSort(), NODE_KIND::NT_SELECT, l, r);
    }
    /*
    (store Array Int Int), return Array
    */
    std::shared_ptr<DAGNode> Parser::mkStore(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isArray() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(l->getSort(), NODE_KIND::NT_STORE, l, r, v);
    }
    // STRINGS COMMON OPERATORS
    /*
    (str.len Str), return Nat
    */
    std::shared_ptr<DAGNode> Parser::mkStrLen(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCStr()){
            return mkConstInt(param->toString().size());
        }

        return mkOper(NAT_SORT, NODE_KIND::NT_STR_LEN, param);
    }
    /*
    (str.++ Str Str+), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(STR_SORT, NODE_KIND::NT_STR_CONCAT, new_params);
    }
    /*
    (str.substr Str Int Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrSubstr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isInt() || !s->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCInt() && s->isCInt()){
            return mkConstStr(strSubstr(l->toString(), r->toInt(), s->toInt()));
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_SUBSTR, l, r, s);
    }
    /*
    (str.prefixof Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrPrefixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return strPrefixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_PREFIXOF, l, r);
    }
    /*
    (str.suffixof Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrSuffixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return strSuffixof(l->toString(), r->toString()) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_SUFFIXOF, l, r);
    }
    /*
    (str.indexof Str Str Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrIndexof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr() || !s->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr() && s->isCInt()){
            return mkConstInt(strIndexof(l->toString(), r->toString(), s->toInt()));
        }

        return mkOper(INT_SORT, NODE_KIND::NT_STR_INDEXOF, l, r, s);
    }
    /*
    (str.at Str Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrCharat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCInt()){
            return mkConstStr(strCharAt(l->toString(), r->toInt()));
        }

        return mkOper(STR_SORT, NODE_KIND::NT_STR_CHARAT, l, r);
    }
    /*
    (str.update Str Int Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrUpdate(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isInt() || !v->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCInt() && v->isCStr()){
            return mkConstStr(strUpdate(l->toString(), r->toInt(), v->toString()));
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_UPDATE, l, r, v);
    }
    /*
    (str.replace Str Str Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplace(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr() || !v->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr() && v->isCStr()){
            return mkConstStr(strReplace(l->toString(), r->toString(), v->toString()));
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE, l, r, v);
    }
    /*
    (str.replace_all Str Str Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplaceAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr() || !v->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr() && v->isCStr()){
            return mkConstStr(strReplaceAll(l->toString(), r->toString(), v->toString()));
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE_ALL, l, r, v);
    }
    /*
    (str.to_lower Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrToLower(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCStr()){
            return mkConstStr(strToLower(param->toString()));
        }

        return mkOper(STR_SORT, NODE_KIND::NT_STR_TO_LOWER, param);
    }
    /*
    (str.to_upper Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrToUpper(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCStr()){
            return mkConstStr(strToUpper(param->toString()));
        }

        return mkOper(STR_SORT, NODE_KIND::NT_STR_TO_UPPER, param);
    }
    /*
    (str.rev Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrRev(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(param->isCStr()){
            return mkConstStr(strRev(param->toString()));
        }

        return mkOper(STR_SORT, NODE_KIND::NT_STR_REV, param);
    }
    /*
    (str.split Str Str), return (_ Array Int Str)
    */
    std::shared_ptr<DAGNode> Parser::mkStrSplit(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(mkArraySort(INT_SORT, STR_SORT), NODE_KIND::NT_STR_SPLIT, l, r);
    }
    // STRINGS COMP
    /*
    (str.< Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return l->toString() < r->toString() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_LT, l, r);
    }
    /*
    (str.<= Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return l->toString() <= r->toString() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_LE, l, r);
    }
    /*
    (str.> Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return l->toString() > r->toString() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_GT, l, r);
    }
    /*
    (str.>= Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return l->toString() >= r->toString() ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_GE, l, r);
    }
    // STRINGS PROPERTIES
    /*
    (str.in_re Str Reg), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrInReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_IN_REG, l, r);
    }
    /*
    (str.contains Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrContains(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isEqTo(r->getSort())) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        if(l->isCStr() && r->isCStr()){
            return strContains(l->toString(), r->toString()) ? mkTrue() : mkFalse();
        }

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_CONTAINS, l, r);
    }
    /*
    (str.is_digit Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrIsDigit(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(BOOL_SORT, NODE_KIND::NT_STR_IS_DIGIT, param);
    }
    // STRINGS CONVERSION
    std::shared_ptr<DAGNode> Parser::mkStrFromInt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(STR_SORT, NODE_KIND::NT_STR_FROM_INT, param);
    }
    /*
    (str.to_int Str), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrToInt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(INT_SORT, NODE_KIND::NT_STR_TO_INT, param);
    }
    /*
    (str.to_re Str), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkStrToReg(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_STR_TO_REG, param);
    }
    /*
    (str.to_code Str), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrToCode(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(INT_SORT, NODE_KIND::NT_STR_TO_CODE, param);
    }
    /*
    (str.from_code Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrFromCode(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(STR_SORT, NODE_KIND::NT_STR_FROM_CODE, param);
    }
    // STRINGS RE CONSTANTS
    std::shared_ptr<DAGNode> Parser::mkRegNone(){
        return mkConstReg("^$");
    }
    std::shared_ptr<DAGNode> Parser::mkRegAll(){
        return mkConstReg("[\\s\\S]*");
    }
    std::shared_ptr<DAGNode> Parser::mkRegAllChar(){
        return mkConstReg("[\\s]*");
    }
    // STRINGS RE COMMON OPERATORS
    /*
    (re.++ Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(REG_SORT, NODE_KIND::NT_REG_CONCAT, new_params);
    }
    /*
    (re.union Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegUnion(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(REG_SORT, NODE_KIND::NT_REG_UNION, new_params);
    }
    /*
    (re.inter Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegInter(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(!params[i]->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
            new_params.emplace_back(params[i]);
        }

        return mkOper(REG_SORT, NODE_KIND::NT_REG_INTER, new_params);
    }
    /*
    (re.diff Reg Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegDiff(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 2) return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
        if(params[0]->isErr() || params[1]->isErr()) return params[0]->isErr()?params[0]:params[1];
        if(!params[0]->getSort()->isReg() || !params[1]->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_DIFF, params[0], params[1]);
    }
    /*
    (re.* Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegStar(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_STAR, param);
    }
    /*
    (re.+ Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegPlus(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_PLUS, param);
    }
    /*
    (re.opt Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegOpt(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_OPT, param);
    }
    /*
    (re.range Reg Int Int), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegRange(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isReg() || !r->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_RANGE, l, r);
    }
    /*
    (reg.^n Reg Int), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isInt() || !r->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_REPEAT, l, r);
    }
    /*
    (re.loop Reg Int Int), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegLoop(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isReg() || !r->getSort()->isInt() || !s->getSort()->isInt()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_LOOP, l, r, s);
    }
    /*
    (re.comp Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegComplement(std::shared_ptr<DAGNode> param){
        if(param->isErr()) return param;
        if(!param->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(REG_SORT, NODE_KIND::NT_REG_COMPLEMENT, param);
    }
    // STRINGS RE FUNCTIONS
    /*
    (str.replace_re Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isReg() || !v->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(STR_SORT, NODE_KIND::NT_REPLACE_REG, l, r, v);
    }
    /*
    (str.replace_all_re Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isReg() || !v->getSort()->isStr()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(STR_SORT, NODE_KIND::NT_REPLACE_REG_ALL, l, r, v);
    }
    /*
    (str.indexof_re Str Reg), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!l->getSort()->isStr() || !r->getSort()->isReg()) return mkErr(ERROR_TYPE::ERR_TYPE_MIS);

        return mkOper(INT_SORT, NODE_KIND::NT_INDEXOF_REG, l, r);
    }
}