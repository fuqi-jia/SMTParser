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

#include "parser.h"
#include "timing.h"
#include <queue>
#include <stack>
#include "util.h"

namespace SMTParser{

    bool isIntParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && (sort->isInt() || sort->isIntOrReal());}
    bool isRealParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && (sort->isReal() || sort->isIntOrReal());}
    bool isBoolParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isBool();}
    bool isBvParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isBv();}
    bool isFpParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isFp();}
    bool isStrParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isStr();}
    bool isRegParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isReg();}
    bool isArrayParam(std::shared_ptr<DAGNode> param){auto sort = param->getSort(); return sort && sort->isArray();}

    // mk operations
    std::shared_ptr<DAGNode> Parser::mkTrue() { return NodeManager::TRUE_NODE; }
    std::shared_ptr<DAGNode> Parser::mkFalse() { return NodeManager::FALSE_NODE; }
    std::shared_ptr<DAGNode> Parser::mkUnknown() { return NodeManager::UNKNOWN_NODE; }
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
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:
                return true;
            default:
                return false;
        }
    }

    bool canExempt(std::shared_ptr<Sort> l, std::shared_ptr<Sort> r){
        if((l->isInt() || l->isReal()) && (r->isInt() || r->isReal())){
            return true;
        }
        return false;
    }
    std::shared_ptr<Sort> Parser::getSort(const std::vector<std::shared_ptr<DAGNode>>& params){
        std::shared_ptr<Sort> sort = nullptr;
        // use the maximum sort only for int/real
        bool is_int_real_sort = params[0]->getSort()->isInt() || params[0]->getSort()->isReal() 
        ||params[0]->getSort()->isIntOrReal();
        if(is_int_real_sort){
            for(size_t i=0;i<params.size();i++){
                if(params[i]->getSort()->isReal()){
                    sort = SortManager::REAL_SORT;
                    break;
                }
            }
            if(sort == nullptr){
                sort = SortManager::INT_SORT;
            }
        }
        else{
            for(size_t i=0;i<params.size();i++){
                if(!params[i]->isConst()){
                    sort = params[i]->getSort();
                    break;
                }
            }
        }
        // all constant -> nullptr
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
        // fast path
        if(p.size() <= 1) {
            return p;
        }
        if(p.size() == 2) {
            std::vector<std::shared_ptr<DAGNode>> params = p;
            size_t hash0 = params[0]->hashCode();
            size_t hash1 = params[1]->hashCode();
            if(hash0 > hash1) {
                std::swap(params[0], params[1]);
            }
            return params;
        }
        if(p.size() == 3) {
            std::vector<std::shared_ptr<DAGNode>> params = p;
            size_t hash0 = params[0]->hashCode();
            size_t hash1 = params[1]->hashCode();
            size_t hash2 = params[2]->hashCode();
            
            // 简单的3元素排序网络
            if(hash0 > hash1) { std::swap(params[0], params[1]); std::swap(hash0, hash1); }
            if(hash1 > hash2) { std::swap(params[1], params[2]); std::swap(hash1, hash2); }
            if(hash0 > hash1) { std::swap(params[0], params[1]); }
            
            return params;
        }
        
        // large case
        std::vector<std::shared_ptr<DAGNode>> params = p;
        
        // pre-compute hash code
        std::vector<std::pair<std::shared_ptr<DAGNode>, size_t>> params_with_hash;
        params_with_hash.reserve(params.size());
        
        for(const auto& param : params) {
            params_with_hash.emplace_back(param, param->hashCode());
        }
        
        // sort by hash code
        std::sort(params_with_hash.begin(), params_with_hash.end(), 
                 [](const std::pair<std::shared_ptr<DAGNode>, size_t> &a, 
                    const std::pair<std::shared_ptr<DAGNode>, size_t> &b){
                     return a.second < b.second;
                 });
        
        // extract sorted nodes
        for(size_t i = 0; i < params_with_hash.size(); i++) {
            params[i] = params_with_hash[i].first;
        }
        
        return params;
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p){
        // simplify
        auto res = simp_oper(t, p);
        if(!res->isUnknown()){
            return res;
        }
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(p);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        auto res = simp_oper(t, l, r);
        if(!res->isUnknown()){
            return res;
        }
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(l);
        params.emplace_back(r);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        auto res = simp_oper(t, l, m, r);
        if(!res->isUnknown()){
            return res;
        }
        std::vector<std::shared_ptr<DAGNode>> params;
        params.emplace_back(l);
        params.emplace_back(m);
        params.emplace_back(r);
        return mkOper(sort, t, params);
    }
    std::shared_ptr<DAGNode> Parser::mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p){
        if(p.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "No parameters for operation", line_number);
            return mkUnknown();
        }
        auto res = simp_oper(t, p);
        if(!res->isUnknown()){
            return res;
        }
        return mkInternalOper(sort, t, p);
    }
    std::shared_ptr<DAGNode> Parser::mkInternalOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p){
        TIME_FUNC();
        // make the params unique
        std::vector<std::shared_ptr<DAGNode>> params(p);
        if(isCommutative(t)){
            params = sortParams(p);
        }
        return node_manager->createNode(sort, t, kindToString(t), params);
    }

    // mk function
    std::shared_ptr<DAGNode> Parser::mkFuncDec(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort){
        if(fun_key_map.find(name)!=fun_key_map.end()){
            // multiple declarations
            err_all(ERROR_TYPE::ERR_MUL_DECL, "Multiple declarations of function", line_number);
            return mkUnknown();
        }
        else{
            // create a new function
            // children: params
            // out_sort: return sort
            std::vector<std::shared_ptr<DAGNode>> children;
            for(auto &param: params){
                // TODO, a random name and not record it.
                std::shared_ptr <DAGNode> param_node = node_manager->createNode(param, NODE_KIND::NT_FUNC_PARAM, param->toString());
                children.emplace_back(param_node);
            }
            // add a NodeManager::NULL_NODE to represent the function body.
            children.insert(children.begin(), NodeManager::NULL_NODE);

            std::shared_ptr<DAGNode> func = node_manager->createNode(out_sort, NODE_KIND::NT_FUNC_DEC, name, children);
            fun_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, func));
            return func;
        }
    }

    std::shared_ptr<DAGNode> Parser::mkFuncDef(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body){
        std::shared_ptr<DAGNode> func = nullptr;
        if(fun_key_map.find(name)!=fun_key_map.end()){
            func = fun_key_map[name];
            condAssert(func->getKind() == NODE_KIND::NT_FUNC_DEC, "mkFuncDef: func is not a function declaration");
            // NOTE: we still check it, even if it is not necessary.
            if(func->getKind() == NODE_KIND::NT_FUNC_DEC){
                // update the function
                func = fun_key_map[name];
                func->updateFuncDef(out_sort, body, params);
                return func;
            }
            else{
                // multiple definitions
                err_all(ERROR_TYPE::ERR_MUL_DEF, "Multiple definitions of function", line_number);
                return mkUnknown();
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
            std::shared_ptr<DAGNode> func = node_manager->createNode(out_sort, NODE_KIND::NT_FUNC_DEF, name, children);
            fun_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, func));
            return func;
        }
    }


    std::shared_ptr<Sort> Parser::mkSortDec(const std::string &name, const size_t &arity){
        return sort_manager->createSortDec(name, arity);
    }

    std::shared_ptr<Sort> Parser::mkSortDef(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort){
        return sort_manager->createSortDef(name, params, out_sort);
    }
    std::shared_ptr<Sort> Parser::mkIntSort(){
        return SortManager::INT_SORT;
    }
    std::shared_ptr<Sort> Parser::mkRealSort(){
        return SortManager::REAL_SORT;
    }
    std::shared_ptr<Sort> Parser::mkBoolSort(){
        return SortManager::BOOL_SORT;
    }
    std::shared_ptr<Sort> Parser::mkStrSort(){
        return SortManager::STR_SORT;
    }
    std::shared_ptr<Sort> Parser::mkRegSort(){
        return SortManager::REG_SORT;
    }
    std::shared_ptr<Sort> Parser::mkRoundingModeSort(){
        return SortManager::ROUNDING_MODE_SORT;
    }
    std::shared_ptr<Sort> Parser::mkNatSort(){
        return SortManager::NAT_SORT;
    }
    std::shared_ptr<Sort> Parser::mkBVSort(const size_t &width){
        return sort_manager->createBVSort(width);
    }
    std::shared_ptr<Sort> Parser::mkFPSort(const size_t &e, const size_t &s){
        return sort_manager->createFPSort(e, s);
    }
    std::shared_ptr<Sort> Parser::mkArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem){
        return sort_manager->createArraySort(index, elem);
    }

    // CORE OPERATORS
    /*
    (= A A+ :chainable), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in eq, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in equality", line_number);
                return mkUnknown();
            }
        }
        
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
            condAssert(l->getChildrenSize() == 1, "mkEq: l has more than one child");
            condAssert(r->getChildrenSize() == 1, "mkEq: r has more than one child");
            return mkEq(l->getChild(0), r->getChild(0));
        }
        else{
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_EQ, l, r);
        }
    }
    std::shared_ptr<DAGNode> Parser::mkEq(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for equality", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkEq(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in eq, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in equality", line_number);
                    return mkUnknown();
                }
            }
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
            if(new_params.size() > 100){
                // [OPTIMIZE] have not use mkOper, because it will sort parameters
                return node_manager->createNode(SortManager::BOOL_SORT, NODE_KIND::NT_EQ, "eq", new_params);
            }
            else{
                return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_EQ, new_params);
            }
        }
    }
    /*
    (distinct A A+ :std::pairwise), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkDistinct(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in distinct, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(l, "Type mismatch in distinct", line_number);
                err_all(r, "Type mismatch in distinct", line_number);
                return mkUnknown();
            }
        }

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
            condAssert(l->getChildrenSize() == 1, "mkDistinct: l has more than one child");
            condAssert(r->getChildrenSize() == 1, "mkDistinct: r has more than one child");
            return mkDistinct(l->getChild(0), r->getChild(0));
        }
        else if(l->isNot()){
            return mkDistinct(l->getChild(0), r);
        }
        else if(r->isNot()){
            return mkDistinct(l, r->getChild(0));
        }
        else{
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_DISTINCT, l, r);
        }
    }
    std::shared_ptr<DAGNode> Parser::mkDistinct(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for distinct", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in distinct, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in distinct", line_number);
                    return mkUnknown();
                }
            }
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
            // for large distinct, create node directly without sorting parameters
            // the semantics of distinct does not depend on the order of parameters, and sorting is too expensive
            if(new_params.size() > 100) {
                // [OPTIMIZE] have not use mkOper, because it will sort parameters
                return node_manager->createNode(SortManager::BOOL_SORT, NODE_KIND::NT_DISTINCT, "distinct", new_params);
            } else {
                return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_DISTINCT, new_params);
            }
        }
    }
    // CONST
    std::shared_ptr<DAGNode> Parser::declareVar(const std::string &name, const std::string &sort){
        return mkVar(sort_key_map[sort], name);
    }
    std::shared_ptr<DAGNode> Parser::declareVar(const std::string &name, const std::shared_ptr<Sort> &sort){
        return mkVar(sort, name);
    }

    // LET
    std::shared_ptr<DAGNode> Parser::mkLetBindVar(const std::string& name, const std::shared_ptr<DAGNode>& expr){
        
        if(preserving_let_key_map.find(name)!=preserving_let_key_map.end()){
            // multiple declarations
            return preserving_let_key_map[name];
        }
        else{
            std::vector<std::shared_ptr<DAGNode>> children;
            children.emplace_back(expr);
            std::shared_ptr<DAGNode> new_var = node_manager->createNode(expr->getSort(), NODE_KIND::NT_LET_BIND_VAR, name, children);
            preserving_let_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, new_var));
            return new_var;
        }
    }

    std::shared_ptr<DAGNode> Parser::mkLetBindVarList(const std::vector<std::shared_ptr<DAGNode>>& bind_vars){
        // empty is allowed
        
        // Use the sort of the first binding variable for the list
        std::shared_ptr<Sort> list_sort = bind_vars[0]->getSort();
        return node_manager->createNode(list_sort, NODE_KIND::NT_LET_BIND_VAR_LIST, "", bind_vars);
    }

    std::shared_ptr<DAGNode> Parser::mkLetChain(const std::vector<std::shared_ptr<DAGNode>>& bind_var_lists, const std::shared_ptr<DAGNode>& body){
        if(!body){
            return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
        }
        
        // Create children: [bind_var_lists..., body]
        std::vector<std::shared_ptr<DAGNode>> children;
        for(const auto& list : bind_var_lists){
            children.emplace_back(list);
        }
        children.emplace_back(body);
        
        return node_manager->createNode(body->getSort(), NODE_KIND::NT_LET_CHAIN, "", children);
    }

    std::shared_ptr<DAGNode> Parser::mkConstInt(const Integer &v){
        std::string v_str = ConversionUtils::toString(v);
        return node_manager->createNode(SortManager::INTOREAL_SORT, NODE_KIND::NT_CONST, v_str);
    }
    std::shared_ptr<DAGNode> Parser::mkConstInt(const std::string &v){
        return mkConstInt(Integer(v));
    }
    std::shared_ptr<DAGNode> Parser::mkConstInt(const int& v){
        return mkConstInt(Integer(v));
    }
    std::shared_ptr<DAGNode> Parser::mkConstInt(const Number& v){
        return mkConstInt(v.toInteger());
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const std::string &v){
        condAssert(TypeChecker::isReal(v) || v == "e" || v == "pi", "mkConstReal: invalid real constant");
        if(v == "e") return NodeManager::E_NODE;
        if(v == "pi") return NodeManager::PI_NODE;
        return node_manager->createNode(SortManager::REAL_SORT, NODE_KIND::NT_CONST, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const Real &v){
        std::string v_str = ConversionUtils::toString(v);
        return node_manager->createNode(SortManager::REAL_SORT, NODE_KIND::NT_CONST, v_str);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const double &v){
        std::string v_str = std::to_string(v);
        return node_manager->createNode(SortManager::REAL_SORT, NODE_KIND::NT_CONST, v_str);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const Integer &v){
        std::string v_str = ConversionUtils::toString(v);
        return node_manager->createNode(SortManager::REAL_SORT, NODE_KIND::NT_CONST, v_str);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReal(const Number& v){
        return mkConstReal(v.toReal());
    }
    std::shared_ptr<DAGNode> Parser::mkConstStr(const std::string &v){
        // process the escape characters in the string
        std::string processed_v = v;
        // if the string is quoted, remove the quotes
        if (v.length() >= 2 && v[0] == '"' && v[v.length()-1] == '"') {
            processed_v = ConversionUtils::unescapeString(v.substr(1, v.length()-2));
            processed_v = "\"" + ConversionUtils::escapeString(processed_v) + "\"";
        }
        return node_manager->createNode(SortManager::STR_SORT, NODE_KIND::NT_CONST, processed_v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstBv(const std::string &v, const size_t& width){
        std::string sort_key_name = "BV_" + std::to_string(width);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = sort_manager->createBVSort(width);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        std::string bv_v = BitVectorUtils::natToBv(v, width);
        return node_manager->createNode(sort, NODE_KIND::NT_CONST, bv_v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstFp(const std::string &v, const size_t& e, const size_t& s){
        std::string sort_key_name = "FP_" + std::to_string(e) + "_" + std::to_string(s);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = sort_manager->createFPSort(e, s);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return node_manager->createNode(sort, NODE_KIND::NT_CONST, v);
    }
    std::shared_ptr<DAGNode> Parser::mkConstFP(const std::string &fp_expr){
        return node_manager->createNode(nullptr, NODE_KIND::NT_CONST, fp_expr);
    }
    std::shared_ptr<DAGNode> Parser::mkConstReg(const std::string &v){
        return node_manager->createNode(SortManager::REG_SORT, NODE_KIND::NT_CONST, v);
    }
    
    std::shared_ptr<DAGNode> Parser::mkRoundingMode(const std::string &mode){
        // Create a special sort for rounding mode
        std::shared_ptr<Sort> rounding_mode_sort = std::make_shared<Sort>(SORT_KIND::SK_ROUNDING_MODE, "RoundingMode", 0);
        return node_manager->createNode(rounding_mode_sort, NODE_KIND::NT_CONST, mode);
    }
    
    // VAR
    std::shared_ptr<DAGNode> Parser::mkTempVar(const std::shared_ptr<Sort>& sort){
        std::string temp_var_name = "temp_" + std::to_string(temp_var_counter++);
        if(temp_var_names.find(temp_var_name) != temp_var_names.end()){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Temp variable name already exists", line_number);
            return mkUnknown();
        }
        std::shared_ptr<DAGNode> newvar = node_manager->createNode(sort, NODE_KIND::NT_TEMP_VAR, temp_var_name);
        temp_var_names.insert(std::pair<std::string, size_t>(temp_var_name, node_manager->getIndex(newvar)));
        return newvar;
    }
    std::shared_ptr<DAGNode> Parser::mkVar(const std::shared_ptr<Sort>& sort, const std::string &name){
        if(var_names.find(name)!=var_names.end()){
            // multiple declarations
            return node_manager->getNode(var_names[name]);
        }
        else{
            std::shared_ptr<DAGNode> newvar = node_manager->createNode(sort, NODE_KIND::NT_VAR, name);
            var_names.insert(std::pair<std::string, size_t>(name, node_manager->getIndex(newvar)));
            return newvar;
        }
    }

    std::shared_ptr<DAGNode> Parser::mkPlaceholderVar(const std::string &name){
        if(placeholder_var_names.find(name) != placeholder_var_names.end()){
            // placeholder variable already exists
            return node_manager->getNode(placeholder_var_names[name]);
        }
        else{
            // Create new placeholder variable with the specified sort
            std::shared_ptr<Sort> sort = placeholder_var_sort ? placeholder_var_sort : SortManager::REAL_SORT;
            std::shared_ptr<DAGNode> newvar = node_manager->createNode(sort, NODE_KIND::NT_PLACEHOLDER_VAR, name);
            condAssert(newvar->isPlaceholderVar(), "Created placeholder variable is not a placeholder variable");
            placeholder_var_names.insert(std::pair<std::string, size_t>(name, node_manager->getIndex(newvar)));
            return newvar;
        }
    }
    std::shared_ptr<DAGNode> Parser::mkVarBool(const std::string &name){
        return mkVar(SortManager::BOOL_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarInt(const std::string &name){
        return mkVar(SortManager::INT_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarReal(const std::string &name){
        return mkVar(SortManager::REAL_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarBv(const std::string &name, const size_t& width){
        std::string sort_key_name = "BV_" + std::to_string(width);
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = sort_manager->createBVSort(width);
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
            sort = sort_manager->createFPSort(e, s);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkVar(sort, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarStr(const std::string &name){
        return mkVar(SortManager::STR_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkVarReg(const std::string &name){
        return mkVar(SortManager::REG_SORT, name);
    }
    std::shared_ptr<DAGNode> Parser::mkFunParamVar(std::shared_ptr<Sort> sort, const std::string &name){
        std::shared_ptr<DAGNode> newvar = node_manager->createNode(sort, NODE_KIND::NT_FUNC_PARAM, name);
        // do not insert into variables
        // it is a function parameter
        return newvar;
    }
    // ARRAY
    std::shared_ptr<DAGNode> Parser::mkArray(const std::string &name, std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem){
        std::string sort_key_name = "ARRAY_" + index->toString() + "_" + elem->toString();
        std::shared_ptr<Sort> sort = nullptr;
        if(sort_key_map.find(sort_key_name) == sort_key_map.end()){
            sort = sort_manager->createArraySort(index, elem);
            sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
        }
        else{
            sort = sort_key_map[sort_key_name];
        }
        return mkVar(sort, name);
    }
    
    /*
    (as const T) value, return Array
    Creates a constant array where all elements have the same value
    */
    std::shared_ptr<DAGNode> Parser::mkConstArray(std::shared_ptr<Sort> sort, std::shared_ptr<DAGNode> value){
        if(!sort->isArray()) {
            err_all(value, "ConstArray on non-array sort", line_number);
            return mkUnknown();
        }
        
        // Check if value type matches array element type
        std::shared_ptr<Sort> elem_sort = sort->getElemSort();
        std::shared_ptr<Sort> value_sort = value->getSort();
        
        return node_manager->createNode(sort, NODE_KIND::NT_CONST_ARRAY, "const_array", {value});
    }
    
    // BOOLEAN
    /*
    (not Bool), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkNot(std::shared_ptr<DAGNode> param){
        if(!isBoolParam(param)) {
            err_all(param, "Negation on non-boolean", line_number);
            return mkUnknown();
        }
        if (param->isNot()) {
            // reduce nested not
            condAssert(param->getChildrenSize() == 1, "mkNot: param has more than one child");
            return param->getChild(0);
        }
        else if(param->isTrue()){
            return mkFalse();
        }
        else if(param->isFalse()){
            return mkTrue();
        }
        else if(param->isArithComp() || param->isBVComp() || param->isStrComp() || param->isFPComp()){
            return negateComp(param);
        }
        else{
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_NOT, param);
        }
    }
    /*
    (and Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkAnd({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkAnd({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkAnd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "AND on empty parameters, return true" << std::endl;
            return mkTrue();
        }
        else if(params.size() == 1){
            return params[0];
        }
        

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(!isBoolParam(params[i])) {
                err_type_mis("AND on non-boolean", line_number);
                return mkUnknown();
            }
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
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_AND, new_params);
        }
    }
    /*
    (or Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkOr({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkOr({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkOr(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "OR on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }
            
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(!isBoolParam(params[i])) {
                err_type_mis("OR on non-boolean", line_number);
                return mkUnknown();
            }
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
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_OR, new_params);
        }
    }
    /*
    (=> Bool Bool+ :right-assoc), return Bool
    (=> a b c d) <=> (or -a -b -c d)
    */
    std::shared_ptr<DAGNode> Parser::mkImplies(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkImplies({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkImplies(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for implies", line_number);
            return mkUnknown();
        }

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

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IMPLIES, new_params);
    }
    /*
    (xor Bool Bool+ :left-assoc), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkXor({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkXor({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkXor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "XOR on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }

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
            return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_XOR, new_params);
        }
    }
    /*
    (ite Bool A A), return A
    */
    std::shared_ptr<DAGNode> Parser::mkIte(std::shared_ptr<DAGNode> cond, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(cond->isErr()) return cond;
        if(l->isErr()) return l;
        if(r->isErr()) return r;
        return mkOper(l->getSort(), NODE_KIND::NT_ITE, cond, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkIte(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for ite", line_number);
            return mkUnknown();
        }

        return mkIte(params[0], params[1], params[2]);
    }
    // ARITHMATIC COMMON OPERATORS
    /*
    (+ rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkAdd({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkAdd({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for add", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        condAssert(params.size() >= 2, "mkAdd: params has less than 2 elements");
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in add, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in add", line_number);
                    return mkUnknown();
                }
            }
            if(isZero(params[i])){
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        // checking
        if(new_params.size() == 0){
            // all 0 constant
            if(options->isRealTheory()){
                return mkConstReal(0.0);
            }
            else if(options->isIntTheory()){
                return mkConstInt(0);
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in add", line_number);
                return mkUnknown();
            }
        }
        else if(new_params.size() == 1){
            // only one uncertain param
            return new_params[0];
        }
        else{
            if(sort == nullptr){
                if(options->isRealTheory()){
                    sort = SortManager::REAL_SORT;
                }
                else if(options->isIntTheory()){
                    sort = SortManager::INT_SORT;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in add", line_number);
                    return mkUnknown();
                }
            }
            return mkOper(sort, NODE_KIND::NT_ADD, new_params);
        }
    }
    /*
    (* rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkMul({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkMul({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 1){
            return params[0];
        }
        condAssert(params.size() >= 2, "mkMul: params has less than 2 elements");
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in mul, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in mul", line_number);
                    return mkUnknown();
                }
            }
            if(isZero(params[i])){
                if(options->isIntTheory()){
                    return mkConstInt(0);
                }
                else if(options->isRealTheory()){
                    return mkConstReal(0.0);
                }
            }
            else if(isOne(params[i])){
                continue;
            }
            else{
                new_params.emplace_back(params[i]);
            }
        }

        if(new_params.size() == 0){
            // all 1 constant
            if(options->isIntTheory()){
                return mkConstInt(1);
            }
            else if(options->isRealTheory()){
                return mkConstReal(1.0);
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in mul", line_number);
                return mkUnknown();
            }
        }
        else if(new_params.size() == 1){
            // only one uncertain param
            return new_params[0];
        }
        else{
            if(sort == nullptr){
                if(options->isRealTheory()){
                    sort = SortManager::REAL_SORT;
                }
                else if(options->isIntTheory()){
                    sort = SortManager::INT_SORT;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in mul", line_number);
                    return mkUnknown();
                }
            }
            if(new_params.size() == 2){
                if(new_params[0]->isCInt() && new_params[1]->isCInt()){
                    return mkConstInt(
                        toInt(new_params[0]) * toInt(new_params[1])
                    );
                }
                else if(new_params[0]->isCReal() && new_params[1]->isCReal()){
                    return mkConstReal(
                        toReal(new_params[0]) * toReal(new_params[1])
                    );
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
        condAssert(params.size() >= 2, "mkIand: params has less than 2 elements");
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in iand, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in iand", line_number);
                    return mkUnknown();
                }
            }

            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            if(options->isRealTheory()){
                sort = SortManager::REAL_SORT;
            }
            else if(options->isIntTheory()){
                sort = SortManager::INT_SORT;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in iand", line_number);
                return mkUnknown();
            }
        }
        if(new_params.size() == 2){
            if(new_params[0]->isCInt() && new_params[1]->isCInt()){
                return mkConstInt(
                    toInt(new_params[0]) & toInt(new_params[1])
                );
            }
        }

        return mkOper(sort, NODE_KIND::NT_IAND, new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkPow2(std::shared_ptr<DAGNode> param){
        
        return mkOper(param->getSort(), NODE_KIND::NT_POW2, param);
    }
    std::shared_ptr<DAGNode> Parser::mkPow(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkOper(l->getSort(), NODE_KIND::NT_POW, l, r);
    }
    /*
    (- rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkSub({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r){
        return mkSub({l, m, r});
    }
    std::shared_ptr<DAGNode> Parser::mkSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for sub", line_number);
            return mkUnknown();
        }
        if(params.size() == 1){
            return mkNeg(params[0]);
        }

        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;
        // (- a b c)
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in sub, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(params[i], "Type mismatch in sub", line_number);
                    return mkUnknown();
                }
            }
            new_params.emplace_back(params[i]);
        }
        if(sort == nullptr){
            if(options->isRealTheory()){
                sort = SortManager::REAL_SORT;
            }
            else if(options->isIntTheory()){
                sort = SortManager::INT_SORT;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in sub", line_number);
                return mkUnknown();
            }
        }
        if(new_params.size() == 2){
            if((sort->isInt() || sort->isIntOrReal()) && new_params[0]->isCInt() && new_params[1]->isCInt()){
                return mkConstInt(
                    toInt(new_params[0]) - toInt(new_params[1])
                );
            }
            else if(sort->isReal() && new_params[0]->isCReal() && new_params[1]->isCReal()){
                return mkConstReal(
                    toReal(new_params[0]) - toReal(new_params[1])
                );
            }
            else if(isZero(new_params[0])){
                return mkNeg(new_params[1]);
            }
            else if(isZero(new_params[1])){
                return new_params[0];
            }
        }
        return mkOper(sort, NODE_KIND::NT_SUB, new_params);
    }
    /*
    (- rt), return rt
    */  
    std::shared_ptr<DAGNode> Parser::mkNeg(std::shared_ptr<DAGNode> param){
        
        return mkOper(param->getSort(), NODE_KIND::NT_NEG, param);
    }
    /*
    (div Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkDivInt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if((!isIntParam(l) || !isIntParam(r))) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in div_int, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in div", line_number);
                return mkUnknown();
            }
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_DIV_INT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkDivInt(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for div", line_number);
            return mkUnknown();
        }
        if(params.size() == 1){
            return params[0];
        }
        if(params.size() == 2){
            return mkDivInt(params[0], params[1]);
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_DIV_INT, params);
    }
    /*
    (/ Real Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkDiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        return mkDivReal({l, r});
    }
    std::shared_ptr<DAGNode> Parser::mkDiv(const std::vector<std::shared_ptr<DAGNode>> &params){
        return mkDivReal(params);
    }
    std::shared_ptr<DAGNode> Parser::mkDivReal(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if((!isRealParam(l) || !isRealParam(r))) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in div_real, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in div", line_number);
                return mkUnknown();
            }
        }
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_DIV_REAL, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkDivReal(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for div", line_number);
            return mkUnknown();
        }
        if(params.size() == 1){
            return params[0];
        }
        if(params.size() == 2){
            return mkDivReal(params[0], params[1]);
        }
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_DIV_REAL, params);
    }
    /*
    (mod Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkMod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isIntParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in mod", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_MOD, l, r);
    }
    /*
    (abs Int), return Int
    (abs Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAbs(std::shared_ptr<DAGNode> param){
        if(!isIntParam(param) && !isRealParam(param)) {
            err_all(param, "Absolute value on non-integer or non-real", line_number);
            return mkUnknown();
        }
        return mkOper(param->getSort(), NODE_KIND::NT_ABS, param);
    }
    /*
    (sqrt Real), return Real
    (sqrt Int), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSqrt(std::shared_ptr<DAGNode> param){
        if(!isIntParam(param) && !isRealParam(param)) {
            err_all(param, "Square root on non-integer or non-real", line_number);
            return mkUnknown();
        }
        return mkOper(param->getSort(), NODE_KIND::NT_SQRT, param);
    }
    /*
    (safesqrt Real), return Real
    (safesqrt Int), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSafeSqrt(std::shared_ptr<DAGNode> param){
        if(!isIntParam(param) && !isRealParam(param)) {
            err_all(param, "Safe square root on non-integer or non-real", line_number);
            return mkUnknown();
        }
        return mkOper(param->getSort(), NODE_KIND::NT_SAFESQRT, param);
    }
    /*
    (ceil Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkCeil(std::shared_ptr<DAGNode> param){
        if(!isIntParam(param) && !isRealParam(param)) {
            err_all(param, "Ceiling on non-integer or non-real", line_number);
            return mkUnknown();
        }
        return mkOper(param->getSort(), NODE_KIND::NT_CEIL, param);
    }
    /*
    (floor Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkFloor(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_FLOOR, param);
    }
    /*
    (round Real), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkRound(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_ROUND, param);
    }
    // TRANSCENDENTAL ARITHMATIC
    /*
    (exp Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkExp(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_EXP, param);
    }
    /*
    (ln Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLn(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_LN, param);
    }
    /*
    (lb Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLb(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_LB, param);
    }
    /*
    (lg Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLg(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_LG, param);
    }
    /*
    (log Real Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkLog(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in log, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in log", line_number);
                return mkUnknown();
            }
        }
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_LOG, l, r);
    }
    /*
    (sin Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSin(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_SIN, param);
    }
    /*
    (cos Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCos(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_COS, param);
    }
    /*
    (sec Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSec(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_SEC, param);
    }
    /*
    (csc Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCsc(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_CSC, param);
    }
    /*
    (tan Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkTan(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_TAN, param);
    }
    /*
    (cot Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCot(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_COT, param);
    }
    /*
    (asin Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsin(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ASIN, param);
    }
    /*
    (acos Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcos(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACOS, param);
    }
    /*
    (asec Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsec(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ASEC, param);
    }
    /*
    (acsc Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcsc(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACSC, param);
    }
    /*
    (atan Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAtan(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ATAN, param);
    }
    /*
    (acot Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcot(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACOT, param);
    }
    /*
    (sinh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSinh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_SINH, param);
    }
    /*
    (cosh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCosh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_COSH, param);
    }
    /*
    (tanh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkTanh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_TANH, param);
    }
    /*
    (sech Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkSech(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_SECH, param);
    }
    /*
    (csch Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCsch(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_CSCH, param);
    }
    /*
    (coth Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkCoth(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_COTH, param);
    }
    /*
    (asinh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsinh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ASINH, param);
    }
    /*
    (acosh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcosh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACOSH, param);
    }
    /*
    (atanh Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAtanh(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ATANH, param);
    }
    /*
    (asech Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAsech(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ASECH, param);
    }
    /*
    (acsch Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcsch(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACSCH, param);
    }
    /*
    (acoth Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAcoth(std::shared_ptr<DAGNode> param){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ACOTH, param);
    }
    /*
    (atan2 Real Real), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkAtan2(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_ATAN2, l, r);
    }
    // ARITHMATIC COMP
    /*
    (<= rt rt+), return rt
    */
    std::shared_ptr<DAGNode> Parser::mkLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in le, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in le", line_number);
                return mkUnknown();
            }
        }
        else if(l == r){
            return mkTrue();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_LE, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in lt, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in lt", line_number);
                return mkUnknown();
            }
        }
        else if(l == r){
            return mkFalse();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_LT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in ge, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in ge", line_number);
                return mkUnknown();
            }
        }
        else if(l == r){
            return mkTrue();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_GE, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!l->getSort()->isEqTo(r->getSort())) {
            if(canExempt(l->getSort(), r->getSort())){
                std::cerr << "Type mismatch in gt, but now exempt for int/real"<<std::endl;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in gt", line_number);
                return mkUnknown();
            }
        }
        else if(l == r){
            return mkFalse();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_GT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkLe(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for le", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkLe(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (<= a b c d) <=> (and (<= a b) (<= b c) (<= c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in le, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in le", line_number);
                    return mkUnknown();
                }
            }
            std::shared_ptr<DAGNode> le = mkLe(params[i], params[i + 1]);
            if(le->isErr()) return le;
            new_params.emplace_back(le);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkLt(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for lt", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkLt(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (< a b c d) <=> (and (< a b) (< b c) (< c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in lt, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in lt", line_number);
                    return mkUnknown();
                }
            }
            std::shared_ptr<DAGNode> lt = mkLt(params[i], params[i + 1]);
            if(lt->isErr()) return lt;
            new_params.emplace_back(lt);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkGe(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for ge", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkGe(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (>= a b c d) <=> (and (>= a b) (>= b c) (>= c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in ge, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in ge", line_number);
                    return mkUnknown();
                }
            }
            std::shared_ptr<DAGNode> ge = mkGe(params[i], params[i + 1]);
            if(ge->isErr()) return ge;
            new_params.emplace_back(ge);
        }

        return mkAnd(new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkGt(const std::vector<std::shared_ptr<DAGNode>>& params){
        if(params.size() < 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for gt", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkGt(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (> a b c d) <=> (and (> a b) (> b c) (> c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in gt, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in gt", line_number);
                    return mkUnknown();
                }
            }
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
        
        if(!isRealParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in to_int", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_TO_INT, param);
    }
    /*
    (to_real Int), return Real
    */
    std::shared_ptr<DAGNode> Parser::mkToReal(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in to_real", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_TO_REAL, param);
    }
    // ARITHMATIC PROPERTIES
    /*
    (is_int Real), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsInt(std::shared_ptr<DAGNode> param){
        
        if(!isRealParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in is_int", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IS_INT, param);
    }
    /*
    (is_divisible Int Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsDivisible(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isIntParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in is_divisible", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IS_DIVISIBLE, l, r);
    }
    /*
    (is_prime Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsPrime(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in is_prime", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IS_PRIME, param);
    }
    /*
    (is_even Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsEven(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in is_even", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IS_EVEN, param);
    }
    /*
    (is_odd Int), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkIsOdd(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in is_odd", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_IS_ODD, param);
    }
    // ARITHMATIC CONSTANTS
    std::shared_ptr<DAGNode> Parser::mkPi(){
        return NodeManager::PI_NODE;
    }
    std::shared_ptr<DAGNode> Parser::mkE(){
        return NodeManager::E_NODE;
    }
    std::shared_ptr<DAGNode> Parser::mkInfinity(std::shared_ptr<Sort> sort){
        if(sort->isEqTo(SortManager::STR_SORT)){
            return NodeManager::STR_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::INT_SORT)){
            return NodeManager::INT_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::REAL_SORT)){
            return NodeManager::REAL_INF_NODE;
        }
        else{
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in infinity", line_number);
            return mkUnknown();
        }
    }
    std::shared_ptr<DAGNode> Parser::mkPosInfinity(std::shared_ptr<Sort> sort){
        if(sort->isEqTo(SortManager::STR_SORT)){
            return NodeManager::STR_POS_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::INT_SORT)){
            return NodeManager::INT_POS_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::REAL_SORT)){
            return NodeManager::REAL_POS_INF_NODE;
        }
        else{
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in pos_infinity", line_number);
            return mkUnknown();
        }
    }
    std::shared_ptr<DAGNode> Parser::mkNegInfinity(std::shared_ptr<Sort> sort){
        if(sort->isEqTo(SortManager::STR_SORT)){
            return NodeManager::STR_NEG_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::INT_SORT)){
            return NodeManager::INT_NEG_INF_NODE;
        }
        else if(sort->isEqTo(SortManager::REAL_SORT)){
            return NodeManager::REAL_NEG_INF_NODE;
        }
        else{
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in neg_infinity", line_number);
            return mkUnknown();
        }
    }
    std::shared_ptr<DAGNode> Parser::mkNan(){
        return NodeManager::NAN_NODE;
    }
    std::shared_ptr<DAGNode> Parser::mkEpsilon(){
        return NodeManager::EPSILON_NODE;
    }
    std::shared_ptr<DAGNode> Parser::mkPosEpsilon(){
        return NodeManager::POS_EPSILON_NODE;
    }
    std::shared_ptr<DAGNode> Parser::mkNegEpsilon(){
        return NodeManager::NEG_EPSILON_NODE;
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
        
        if(!isIntParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in gcd", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_GCD, l, r);
    }
    /*
    (lcm Int Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkLcm(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isIntParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in lcm", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_LCM, l, r);
    }
    /*
    (factorial Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkFact(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in factorial", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_FACT, param);
    }
    // BITVECTOR COMMON OPERATORS
    /*
    (bv_not Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNot(std::shared_ptr<DAGNode> param){
        
        if(!isBvParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_not", line_number);
            return mkUnknown();
        }
        return mkOper(param->getSort(), NODE_KIND::NT_BV_NOT, param);
    }
    /*
    (bvand Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_and", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_AND, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvAnd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVAND on empty parameters, return true" << std::endl;
            return mkTrue();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvAnd(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_and", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_AND, new_params);
    }
    /*
    (bvor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_or", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_OR, l, r);
    }
    /*
    (bvor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvOr(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVOR on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvOr(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_or", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_OR, new_params);

    }
    std::shared_ptr<DAGNode> Parser::mkBvXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_xor", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_XOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvXor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVXOR on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvXor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_xor", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_XOR, new_params);
    }
    /*
    (bvnand Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNand(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_nand", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_NAND, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvNand(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVNAND on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvNand(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_nand", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_NAND, new_params);
    }
    /*
    (bvnor Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_nor", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_NOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvNor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVNOR on empty parameters, return true" << std::endl;
            return mkTrue();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvNor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_nor", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_NOR, new_params);
    }
    /*
    (bvxnor Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvXnor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_xnor", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_XNOR, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvXnor(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            std::cerr << "BVXNOR on empty parameters, return false" << std::endl;
            return mkFalse();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        if(params.size() == 2){
            return mkBvXnor(params[0], params[1]);
        }

        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_xnor", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_XNOR, new_params);
    }
    /*
    (bvcomp Bv Bv), return (_ BitVec 1)
    */
    std::shared_ptr<DAGNode> Parser::mkBvComp(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_comp", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> sort = sort_manager->createBVSort(1);

        return mkOper(sort, NODE_KIND::NT_BV_COMP, l, r);
    }
    /*
    (bvneg Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvNeg(std::shared_ptr<DAGNode> param){
        
        return mkOper(param->getSort(), NODE_KIND::NT_BV_NEG, param);
    }
    /*
    (bvadd Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_add", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_ADD, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for bv_add", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvAdd(params[0], params[1]);
        }

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_add", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_ADD, new_params);
    }
    /*
    (bvsub Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sub", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_SUB, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for bv_sub", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvSub(params[0], params[1]);
        }

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sub", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_SUB, new_params);
    }
    /*
    (bvmul Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_mul", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_MUL, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkBvMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for bv_mul", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        if(params.size() == 2){
            return mkBvMul(params[0], params[1]);
        }

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_mul", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_BV_MUL, new_params);
    }
    /*
    (bvudiv Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvUdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_udiv", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_UDIV, l, r);
    }
    /*
    (bvurem Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvUrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_urem", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_UREM, l, r);
    }
    /*
    (bvumod Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvUmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_umod", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_UMOD, l, r);
    }
    /*
    (bvsdiv Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sdiv", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_SDIV, l, r);
    }
    /*
    (bvsrem Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_srem", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_SREM, l, r);
    }
    /*
    (bvsmod Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_smod", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_SMOD, l, r);
    }
    /*
    (bvshl Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvShl(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_shl", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_SHL, l, r);
    }
    /*
    (bvlshr Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvLshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_lshr", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_LSHR, l, r);
    }
    /*
    (bvashr Bv Bv), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvAshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_ashr", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_BV_ASHR, l, r);
    }
    /*
    (bvconcat Bv Bv+), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for bv_concat", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::vector<std::shared_ptr<DAGNode>> new_params;

        size_t width = 0;
        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            // no need to check equal sort
            if(!isBvParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_concat", line_number);
                return mkUnknown();
            }
            width += params[i]->getSort()->getBitWidth();
            new_params.emplace_back(params[i]);
        }
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_CONCAT, new_params);
    }
    /*
    (bvextract Bv Int Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvExtract(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!isBvParam(l) || !isIntParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_extract", line_number);
            return mkUnknown();
        }
        size_t width = toInt(r).toULong() - toInt(s).toULong() + 1;
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_EXTRACT, l, r, s);
    }
    /*
    (bvrepeat Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_repeat", line_number);
            return mkUnknown();
        }
        size_t width = l->getSort()->getBitWidth() * toInt(r).toULong();
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_REPEAT, l, r);
    }
    /*
    (zero_extend Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvZeroExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_zero_ext", line_number);
            return mkUnknown();
        }
        size_t width = toInt(r).toULong();
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);
        return mkOper(new_sort, NODE_KIND::NT_BV_ZERO_EXT, l, r);
    }
    /*
    (bvsign_extend Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvSignExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sign_ext", line_number);
            return mkUnknown();
        }
        size_t width = toInt(r).toULong();
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_SIGN_EXT, l, r);
    }
    /*
    (bvrotate_left Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRotateLeft(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_rotate_left", line_number);
            return mkUnknown();
        }

        size_t width = l->getSort()->getBitWidth();
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_ROTATE_LEFT, l, r);
    }
    /*
    (bvrotate_right Bv Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkBvRotateRight(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_rotate_right", line_number);
            return mkUnknown();
        }
        size_t width = l->getSort()->getBitWidth();
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(width);

        return mkOper(new_sort, NODE_KIND::NT_BV_ROTATE_RIGHT, l, r);
    }
    // BITVECTOR COMP
    /*
    (bvult Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_ult", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_ULT, l, r);
    }
    /*
    (bvule Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_ule", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_ULE) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkTrue();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_ULE, l, r);
    }
    /*
    (bvugt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_ugt", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_UGT) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkFalse();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_UGT, l, r);
    }
    /*
    (bvuge Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvUge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_uge", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_UGE) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkTrue();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_UGE, l, r);
    }
    /*
    (bvslt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_slt", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SLT) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkFalse();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_SLT, l, r);
    }
    /*
    (bvsle Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sle", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SLE) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkTrue();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_SLE, l, r);
    }
    /*
    (bvsgt Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sgt", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SGT) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkFalse();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_SGT, l, r);
    }
    /*
    (bvsge Bv Bv), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkBvSge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isBvParam(l) || !isBvParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_sge", line_number);
            return mkUnknown();
        }

        if(l->isCBV() && r->isCBV()){
            return BitVectorUtils::bvComp(l->toString(), r->toString(), NODE_KIND::NT_BV_SGE) ? mkTrue() : mkFalse();
        }
        else if(l == r){
            return mkTrue();
        }


        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_BV_SGE, l, r);
    }
    // BITVECTOR CONVERSION
    /*
    (bv2nat Bv), return Nat
    */
    std::shared_ptr<DAGNode> Parser::mkBvToNat(std::shared_ptr<DAGNode> param){
        
        if(!isBvParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_to_nat", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_BV_TO_NAT, param);
    }
    /*
    (nat2bv Nat Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkNatToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        
        if(!isIntParam(param) || !isIntParam(size)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in nat_to_bv", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(toInt(size).toULong());
        return mkOper(new_sort, NODE_KIND::NT_NAT_TO_BV, param, size);
    }
    /*
    (bv2int Bv), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkBvToInt(std::shared_ptr<DAGNode> param){
        
        if(!isBvParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in bv_to_int", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_BV_TO_INT, param);
    }
    /*
    (int2bv Int Int), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkIntToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        
        if(!isIntParam(param) || !isIntParam(size)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in int_to_bv", line_number);
            return mkUnknown();
        }
        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(toInt(size).toULong());
        return mkOper(new_sort, NODE_KIND::NT_INT_TO_BV, param, size);
    }

    // FLOATING POINT COMMON OPERATORS
    /*
    (fp.add RoundingMode FloatingPoint FloatingPoint), return FloatingPoint
    */
    std::shared_ptr<DAGNode> Parser::mkFpAdd(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "fp.add requires exactly 3 parameters: RoundingMode, FloatingPoint, FloatingPoint", line_number);
            return mkUnknown();
        }
        
        if(params[0]->isErr() || params[1]->isErr() || params[2]->isErr()) {
            return params[0]->isErr() ? params[0] : (params[1]->isErr() ? params[1] : params[2]);
        }
        
        if(!params[0]->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "First parameter of fp.add must be a rounding mode", line_number);
            return mkUnknown();
        }
        
        if(!isFpParam(params[1]) || !isFpParam(params[2])) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Second and third parameters of fp.add must be floating point numbers", line_number);
            return mkUnknown();
        }
        
        std::shared_ptr<Sort> result_sort = params[1]->getSort();
        if(!(*result_sort == *params[2]->getSort())) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Floating point operands must have the same sort", line_number);
            return mkUnknown();
        }
        
        return mkOper(result_sort, NODE_KIND::NT_FP_ADD, params);
    }
    /*
    (fp.sub RoundingMode FloatingPoint FloatingPoint), return FloatingPoint
    */
    std::shared_ptr<DAGNode> Parser::mkFpSub(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "fp.sub requires exactly 3 parameters: RoundingMode, FloatingPoint, FloatingPoint", line_number);
            return mkUnknown();
        }
        
        if(params[0]->isErr() || params[1]->isErr() || params[2]->isErr()) {
            return params[0]->isErr() ? params[0] : (params[1]->isErr() ? params[1] : params[2]);
        }
        
        if(!params[0]->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "First parameter of fp.sub must be a rounding mode", line_number);
            return mkUnknown();
        }
        
        if(!isFpParam(params[1]) || !isFpParam(params[2])) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Second and third parameters of fp.sub must be floating point numbers", line_number);
            return mkUnknown();
        }
        
        std::shared_ptr<Sort> result_sort = params[1]->getSort();
        if(!(*result_sort == *params[2]->getSort())) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Floating point operands must have the same sort", line_number);
            return mkUnknown();
        }
        
        return mkOper(result_sort, NODE_KIND::NT_FP_SUB, params);
    }
    /*
    (fp.mul RoundingMode FloatingPoint FloatingPoint), return FloatingPoint
    */
    std::shared_ptr<DAGNode> Parser::mkFpMul(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "fp.mul requires exactly 3 parameters: RoundingMode, FloatingPoint, FloatingPoint", line_number);
            return mkUnknown();
        }
        
        if(params[0]->isErr() || params[1]->isErr() || params[2]->isErr()) {
            return params[0]->isErr() ? params[0] : (params[1]->isErr() ? params[1] : params[2]);
        }
        
        if(!params[0]->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "First parameter of fp.mul must be a rounding mode", line_number);
            return mkUnknown();
        }
        
        if(!isFpParam(params[1]) || !isFpParam(params[2])) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Second and third parameters of fp.mul must be floating point numbers", line_number);
            return mkUnknown();
        }
        
        std::shared_ptr<Sort> result_sort = params[1]->getSort();
        if(!(*result_sort == *params[2]->getSort())) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Floating point operands must have the same sort", line_number);
            return mkUnknown();
        }
        
        return mkOper(result_sort, NODE_KIND::NT_FP_MUL, params);
    }
    /*
    (fp.div RoundingMode FloatingPoint FloatingPoint), return FloatingPoint
    */
    std::shared_ptr<DAGNode> Parser::mkFpDiv(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 3){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "fp.div requires exactly 3 parameters: RoundingMode, FloatingPoint, FloatingPoint", line_number);
            return mkUnknown();
        }
        
        if(params[0]->isErr() || params[1]->isErr() || params[2]->isErr()) {
            return params[0]->isErr() ? params[0] : (params[1]->isErr() ? params[1] : params[2]);
        }
        
        if(!params[0]->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "First parameter of fp.div must be a rounding mode", line_number);
            return mkUnknown();
        }
        
        if(!isFpParam(params[1]) || !isFpParam(params[2])) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Second and third parameters of fp.div must be floating point numbers", line_number);
            return mkUnknown();
        }
        
        std::shared_ptr<Sort> result_sort = params[1]->getSort();
        if(!(*result_sort == *params[2]->getSort())) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Floating point operands must have the same sort", line_number);
            return mkUnknown();
        }
        
        return mkOper(result_sort, NODE_KIND::NT_FP_DIV, params);
    }
    /*
    (fp.abs Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpAbs(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_abs", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_ABS, param);
    }
    /*
    (fp.neg Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpNeg(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_neg", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_NEG, param);
    }
    /*
    (fp.rem Fp Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpRem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_rem", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort(), NODE_KIND::NT_FP_REM, l, r);
    }
    /*
    (fp.fma RoundingMode Fp Fp Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpFma(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 4) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "fp.fma requires exactly 4 parameters: RoundingMode Fp Fp Fp", line_number);
            return mkUnknown();
        }
        
        // Check if first parameter is rounding mode
        if(!params[0]->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "First parameter must be a rounding mode in fp.fma", line_number);
            return mkUnknown();
        }
        
        // Check if other parameters are floating point
        for(size_t i = 1; i < params.size(); i++) {
            if(params[i]->isErr()) return params[i];
            if(!isFpParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Parameters 2-4 must be floating point in fp.fma", line_number);
                return mkUnknown();
            }
        }
        
        // All floating point parameters should have the same sort
        std::shared_ptr<Sort> sort = params[1]->getSort();
        for(size_t i = 2; i < params.size(); i++) {
            if(!(*params[i]->getSort() == *sort)) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "All floating point parameters must have the same sort in fp.fma", line_number);
                return mkUnknown();
            }
        }

        return mkOper(sort, NODE_KIND::NT_FP_FMA, params);
    }
    /*
    (fp.sqrt RoundingMode Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpSqrt(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param){
        if(rm->isErr() || param->isErr()) return rm->isErr()?rm:param;
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_sqrt", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_SQRT, rm, param);
    }
    /*
    (fp.sqrt Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpSqrt(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_sqrt", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_SQRT, param);
    }
    /*
    (fp.roundToIntegral RoundingMode Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpRoundToIntegral(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param){
        if(rm->isErr() || param->isErr()) return rm->isErr()?rm:param;
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_roundToIntegral", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_ROUND_TO_INTEGRAL, rm, param);
    }
    /*
    (fp.roundToIntegral Fp), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpRoundToIntegral(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_roundToIntegral", line_number);
            return mkUnknown();
        }

        return mkOper(param->getSort(), NODE_KIND::NT_FP_ROUND_TO_INTEGRAL, param);
    }
    /*
    (fp.min Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpMin(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for fp_min", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isFpParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_min", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_FP_MIN, new_params);
    }
    /*
    (fp.max Fp+), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpMax(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for fp_max", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !isFpParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_max", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(sort == nullptr){
            sort = new_params[0]->getSort();
        }

        return mkOper(sort, NODE_KIND::NT_FP_MAX, new_params);
    }
    // FLOATING POINT COMP
    /*
    (fp.leq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_le", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkTrue();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_LE, l, r);
    }
    /*
    (fp.lt Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_lt", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_LT, l, r);
    }
    /*
    (fp.geq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_ge", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkTrue();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_GE, l, r);
    }
    /*
    (fp.gt Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_gt", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_GT, l, r);
    }
    /*
    (fp.eq Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_eq", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkTrue();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_EQ, l, r);
    }
    /*
    (fp.ne Fp Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpNe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!isFpParam(l) || !isFpParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_ne", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_NE, l, r);
    }
    // FLOATING POINT CONVERSION
    /*
    (fp.to_ubv Fp), return Bv
    */
    std::shared_ptr<DAGNode> Parser::mkFpToUbv(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        
        if(!rm->getSort()->isRoundingMode() || !isFpParam(param) || !isIntParam(size)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_to_ubv", line_number);
            return mkUnknown();
        }

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(FloatingPointUtils::fpToUbv(param->toString(), toInt(size)), toInt(size).toULong());
        }

        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(toInt(size).toULong());

        return mkOper(new_sort, NODE_KIND::NT_FP_TO_UBV, rm, param, size);
    }
    std::shared_ptr<DAGNode> Parser::mkFpToSbv(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size){
        
        if(!rm->getSort()->isRoundingMode() || !isFpParam(param) || !isIntParam(size)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_to_sbv", line_number);
            return mkUnknown();
        }

        if(param->isCBV() && size->isCBV()){
            return mkConstBv(FloatingPointUtils::fpToSbv(param->toString(), toInt(size)), toInt(size).toULong());
        }

        std::shared_ptr<Sort> new_sort = sort_manager->createBVSort(toInt(size).toULong());

        return mkOper(new_sort, NODE_KIND::NT_FP_TO_SBV, rm, param, size);
    }
    std::shared_ptr<DAGNode> Parser::mkFpToReal(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_to_real", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REAL_SORT, NODE_KIND::NT_FP_TO_REAL, param);
    }
    /*
    (to_fp eb sb param), return Fp
    Supports:
    1. ((_ to_fp eb sb) RoundingMode Real) -> params: [eb, sb], args: [RoundingMode, Real]
    2. ((_ to_fp eb sb) RoundingMode (_ BitVec m)) -> params: [eb, sb], args: [RoundingMode, BitVec]
    3. ((_ to_fp eb sb) (_ BitVec m)) -> params: [eb, sb], args: [BitVec]
    */
    std::shared_ptr<DAGNode> Parser::mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param){
        if(eb->isErr() || sb->isErr() || rm->isErr() || param->isErr()) return eb->isErr()?eb:(sb->isErr()?sb:(rm->isErr()?rm:param));

        // Validate eb and sb are integers
        if(!eb->isCInt() && !eb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Exponent width must be an integer in to_fp", line_number);
            return mkUnknown();
        }
        if(!sb->isCInt() && !sb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Significand width must be an integer in to_fp", line_number);
            return mkUnknown();
        }

        // Validate rounding mode
        if(!rm->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Third parameter must be a rounding mode in to_fp", line_number);
            return mkUnknown();
        }

        // Get floating point sort
        size_t exponent_width = toInt(eb).toULong();
        size_t significand_width = toInt(sb).toULong();
        std::shared_ptr<Sort> sort = sort_manager->createFPSort(exponent_width, significand_width);

        // Validate param type
        if(!isRealParam(param) && !isBvParam(param) && !isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Fourth parameter must be Real, BitVec, or FloatingPoint in to_fp", line_number);
            return mkUnknown();
        }

        std::vector<std::shared_ptr<DAGNode>> params = {eb, sb, rm, param};
        return mkOper(sort, NODE_KIND::NT_FP_TO_FP, params);
    }

    std::shared_ptr<DAGNode> Parser::mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> param){
        if(eb->isErr() || sb->isErr() || param->isErr()) return eb->isErr()?eb:(sb->isErr()?sb:param);

        // Validate eb and sb are integers
        if(!eb->isCInt() && !eb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Exponent width must be an integer in to_fp", line_number);
            return mkUnknown();
        }
        if(!sb->isCInt() && !sb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Significand width must be an integer in to_fp", line_number);
            return mkUnknown();
        }

        // Get floating point sort
        size_t exponent_width = toInt(eb).toULong();
        size_t significand_width = toInt(sb).toULong();
        std::shared_ptr<Sort> sort = sort_manager->createFPSort(exponent_width, significand_width);

        // Validate param type (must be BitVec for this overload)
        if(!isBvParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Parameter must be BitVec in to_fp", line_number);
            return mkUnknown();
        }

        return mkOper(sort, NODE_KIND::NT_FP_TO_FP, eb, sb, param);
    }
    /*
    ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m)), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkToFpUnsigned(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param){
        if(eb->isErr() || sb->isErr() || rm->isErr() || param->isErr()) return eb->isErr()?eb:(sb->isErr()?sb:(rm->isErr()?rm:param));

        if(!eb->isCInt() && !eb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Exponent width must be an integer in to_fp_unsigned", line_number);
            return mkUnknown();
        }
        if(!sb->isCInt() && !sb->isConst()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Significand width must be an integer in to_fp_unsigned", line_number);
            return mkUnknown();
        }

        size_t exponent_width = toInt(eb).toULong();
        size_t significand_width = toInt(sb).toULong();
        std::shared_ptr<Sort> sort = sort_manager->createFPSort(exponent_width, significand_width);

        if(!rm->getSort()->isRoundingMode()) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Third parameter must be a rounding mode in to_fp_unsigned", line_number);
            return mkUnknown();
        }

        if(!isBvParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Fourth parameter must be BitVec in to_fp_unsigned", line_number);
            return mkUnknown();
        }

        std::vector<std::shared_ptr<DAGNode>> params = {eb, sb, rm, param};
        return mkOper(sort, NODE_KIND::NT_FP_TO_FP_UNSIGNED, params);
    }
    /*
    (fp sign exp mant), return Fp
    */
    std::shared_ptr<DAGNode> Parser::mkFpConst(std::shared_ptr<DAGNode> sign, std::shared_ptr<DAGNode> exp, std::shared_ptr<DAGNode> mant){
        if(sign->isErr() || exp->isErr() || mant->isErr()) return sign->isErr()?sign:(exp->isErr()?exp:mant);

        if(!isBvParam(sign) || !isBvParam(exp) || !isBvParam(mant)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "All parameters must be BitVec in fp constant", line_number);
            return mkUnknown();
        }

        size_t sign_width = sign->getSort()->getBitWidth();
        size_t exp_width = exp->getSort()->getBitWidth();
        size_t mant_width = mant->getSort()->getBitWidth();

        if(sign_width != 1) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Sign bit must be 1 bit wide", line_number);
            return mkUnknown();
        }

        std::shared_ptr<Sort> sort = sort_manager->createFPSort(exp_width, mant_width + 1);
        std::vector<std::shared_ptr<DAGNode>> children = {sign, exp, mant};
        return node_manager->createNode(sort, NODE_KIND::NT_CONST, "(fp_bit_representation)", children);
    }
    // FLOATING POINT PROPERTIES
    /*
    (fp.isNormal Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNormal(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_isNormal", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NORMAL, param);
    }
    /*
    (fp.isSubnormal Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsSubnormal(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_isSubnormal", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_SUBNORMAL, param);
    }
    /*
    (fp.isZero Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsZero(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_isZero", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_ZERO, param);
    }
    /*
    (fp.isInfinite Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsInf(std::shared_ptr<DAGNode> param){
        if(!isFpParam(param)) {
            err_all(param, "Expected floating-point parameter", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_INF, param);
    }
    /*
    (fp.isNaN Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNan(std::shared_ptr<DAGNode> param){
        if(!isFpParam(param)) {
            err_all(param, "Expected floating-point parameter", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NAN, param);
    }
    /*
    (fp.isNegative Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsNeg(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_isNeg", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NEG, param);
    }
    /*
    (fp.isPositive Fp), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkFpIsPos(std::shared_ptr<DAGNode> param){
        
        if(!isFpParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in fp_isPos", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_POS, param);
    }
    // ARRAY
    /*
    (select Array Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkSelect(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isArrayParam(l)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in select", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort()->getElemSort(), NODE_KIND::NT_SELECT, l, r);
    }
    /*
    (store Array Int Int), return Array
    */
    std::shared_ptr<DAGNode> Parser::mkStore(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isArrayParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in store", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STORE, l, r, v);
    }
    // STRINGS COMMON OPERATORS
    /*
    (str.len Str), return Nat
    */
    std::shared_ptr<DAGNode> Parser::mkStrLen(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_len", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_LEN, param);
    }
    /*
    (str.++ Str Str+), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for str_concat", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!isStrParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_concat", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        if(new_params.size() == 0) return mkConstStr("");
        if(new_params.size() == 1) return new_params[0];
        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_CONCAT, new_params);
    }
    /*
    (str.substr Str Int Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrSubstr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isIntParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_substr", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_SUBSTR, l, r, s);
    }
    /*
    (str.prefixof Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrPrefixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_prefixof", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_PREFIXOF, l, r);
    }
    /*
    (str.suffixof Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrSuffixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_suffixof", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_SUFFIXOF, l, r);
    }
    /*
    (str.indexof Str Str Int), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrIndexof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isStrParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_indexof", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_INDEXOF, l, r, s);
    }
    /*
    (str.at Str Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrCharat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_charat", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_CHARAT, l, r);
    }
    /*
    (str.update Str Int Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrUpdate(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isIntParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_update", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_UPDATE, l, r, v);
    }
    /*
    (str.replace Str Str Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplace(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isStrParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_replace", line_number);
            return mkUnknown();
        }

        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE, l, r, v);
    }
    /*
    (str.replace_all Str Str Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplaceAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(!isStrParam(l)) {
            err_all(l, "Expected string parameter", line_number);
            return mkUnknown();
        }
        if(!isStrParam(r)) {
            err_all(r, "Expected string parameter", line_number);
            return mkUnknown();
        }
        if(!isStrParam(v)) {
            err_all(v, "Expected string parameter", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE_ALL, l, r, v);
    }
    /*
    (str.replace_re Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isRegParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_replace_re", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE_REG, l, r, v);
    }

    /*
    (str.replace_re_all Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isRegParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_replace_re_all", line_number);
            return mkUnknown();
        }
        return mkOper(l->getSort(), NODE_KIND::NT_STR_REPLACE_REG_ALL, l, r, v);
    }

    /*
    (str.indexof_re Str Reg), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(l->isErr() || r->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isRegParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_indexof_re", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_INDEXOF_REG, l, r);
    }

    /*
    (str.to_lower Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrToLower(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_to_lower", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_TO_LOWER, param);
    }
    /*
    (str.to_upper Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrToUpper(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_to_upper", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_TO_UPPER, param);
    }
    /*
    (str.rev Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrRev(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_rev", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_REV, param);
    }
    /*
    (str.split Str Str), return (_ Array Int Str)
    */
    std::shared_ptr<DAGNode> Parser::mkStrSplit(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_split", line_number);
            return mkUnknown();
        }
        return mkOper(sort_manager->createArraySort(SortManager::INT_SORT, SortManager::STR_SORT), NODE_KIND::NT_STR_SPLIT, l, r);
    }
    std::shared_ptr<DAGNode> Parser::mkStrSplitAt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(!isStrParam(l) || !isStrParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_split_at", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_SPLIT_AT, l, r, s);
    }
    std::shared_ptr<DAGNode> Parser::mkStrSplitRest(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(!isStrParam(l) || !isStrParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_split_rest", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_SPLIT_REST, l, r, s);
    }
    std::shared_ptr<DAGNode> Parser::mkStrNumSplits(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_num_splits", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_NUM_SPLITS, l, r);
    }
    /*
    (str.split_at_re Str Reg Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrSplitAtRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(!isStrParam(l) || !isRegParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_split_at_re", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_SPLIT_AT_RE, l, r, s);
    }
    /*
    (str.split_rest_re Str Reg Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrSplitRestRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(!isStrParam(l) || !isRegParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_split_rest_re", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_SPLIT_REST_RE, l, r, s);
    }
    /*
    (str.num_splits_re Str Reg), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrNumSplitsRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!isStrParam(l) || !isRegParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_num_splits_re", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_NUM_SPLITS_RE, l, r);
    }
    // STRINGS COMP
    /*
    (str.< Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_lt", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_LT, l, r);
    }
    /*
    (str.<= Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_le", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkTrue();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_LE, l, r);
    }
    /*
    (str.> Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_gt", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkFalse();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_GT, l, r);
    }
    /*
    (str.>= Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_ge", line_number);
            return mkUnknown();
        }
        else if(l == r){
            return mkTrue();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_GE, l, r);
    }
    // STRINGS PROPERTIES
    /*
    (str.in_re Str Reg), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrInReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        if(!isStrParam(l)) {
            err_all(l, "Expected string parameter", line_number);
            return mkUnknown();
        }
        if(!isRegParam(r)) {
            err_all(r, "Expected regex parameter", line_number);
            return mkUnknown();
        }
        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_IN_REG, l, r);
    }
    /*
    (str.contains Str Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrContains(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_contains", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_CONTAINS, l, r);
    }
    /*
    (str.is_digit Str), return Bool
    */
    std::shared_ptr<DAGNode> Parser::mkStrIsDigit(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_is_digit", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_STR_IS_DIGIT, param);
    }
    // STRINGS CONVERSION
    std::shared_ptr<DAGNode> Parser::mkStrFromInt(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_from_int", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_FROM_INT, param);
    }
    /*
    (str.to_int Str), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrToInt(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_to_int", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_TO_INT, param);
    }
    /*
    (str.to_re Str), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkStrToReg(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_to_reg", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_STR_TO_REG, param);
    }
    /*
    (str.to_code Str), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkStrToCode(std::shared_ptr<DAGNode> param){
        
        if(!isStrParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_to_code", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_TO_CODE, param);
    }
    /*
    (str.from_code Int), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkStrFromCode(std::shared_ptr<DAGNode> param){
        
        if(!isIntParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_from_code", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_FROM_CODE, param);
    }
    // STRINGS RE CONSTANTS
    std::shared_ptr<DAGNode> Parser::mkRegNone(){
        return mkConstReg("re.none");
    }
    std::shared_ptr<DAGNode> Parser::mkRegAll(){
        return mkConstReg("re.all");
    }
    std::shared_ptr<DAGNode> Parser::mkRegAllChar(){
        return mkConstReg("re.allchar");
    }
    // STRINGS RE COMMON OPERATORS
    /*
    (re.++ Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegConcat(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for reg_concat", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!isRegParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_concat", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_CONCAT, new_params);
    }
    /*
    (re.union Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegUnion(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for reg_union", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!isRegParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_union", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_UNION, new_params);
    }
    /*
    (re.inter Reg Reg+), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegInter(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for reg_inter", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::vector<std::shared_ptr<DAGNode>> new_params;

        for(size_t i=0;i<params.size();i++){
            if(params[i]->isErr()) return params[i];
            if(!isRegParam(params[i])) {
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_inter", line_number);
                return mkUnknown();
            }
            new_params.emplace_back(params[i]);
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_INTER, new_params);
    }
    /*
    (re.diff Reg Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegDiff(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() != 2) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for reg_diff", line_number);
            return mkUnknown();
        }
        if(params[0]->isErr() || params[1]->isErr()) return params[0]->isErr()?params[0]:params[1];
        if(!isRegParam(params[0]) || !isRegParam(params[1])) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_diff", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_DIFF, params[0], params[1]);
    }
    /*
    (re.* Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegStar(std::shared_ptr<DAGNode> param){
        
        if(!isRegParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_star", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_STAR, param);
    }
    /*
    (re.+ Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegPlus(std::shared_ptr<DAGNode> param){
        
        if(!isRegParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_plus", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_PLUS, param);
    }
    /*
    (re.opt Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegOpt(std::shared_ptr<DAGNode> param){
        
        if(!isRegParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_opt", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_OPT, param);
    }
    /*
    (re.range Str Str), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegRange(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isStrParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_range", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_RANGE, l, r);
    }
    /*
    (reg.^n Reg Int), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        // e.g. (re.^ (str.to.re "a") 3)
        
        if(!isRegParam(l) || !isIntParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_repeat", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_REPEAT, l, r);
    }
    /*
    (re.loop Reg Int Int), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegLoop(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s){
        if(l->isErr() || r->isErr() || s->isErr()) return l->isErr()?l:r;
        if(!isRegParam(l) || !isIntParam(r) || !isIntParam(s)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_loop", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_LOOP, l, r, s);
    }
    /*
    (re.comp Reg), return Reg
    */
    std::shared_ptr<DAGNode> Parser::mkRegComplement(std::shared_ptr<DAGNode> param){
        
        if(!isRegParam(param)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in reg_complement", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::REG_SORT, NODE_KIND::NT_REG_COMPLEMENT, param);
    }
    // STRINGS RE FUNCTIONS
    /*
    (str.replace_re Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isRegParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_replace_re", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_REPLACE_REG, l, r, v);
    }
    /*
    (str.replace_re_all Str Reg Str), return Str
    */
    std::shared_ptr<DAGNode> Parser::mkReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v){
        if(l->isErr() || r->isErr() || v->isErr()) return l->isErr()?l:r;
        if(!isStrParam(l) || !isRegParam(r) || !isStrParam(v)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_replace_re_all", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::STR_SORT, NODE_KIND::NT_STR_REPLACE_REG_ALL, l, r, v);
    }
    /*
    (str.indexof_re Str Reg), return Int
    */
    std::shared_ptr<DAGNode> Parser::mkIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r){
        
        if(!isStrParam(l) || !isRegParam(r)) {
            err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in str_indexof_re", line_number);
            return mkUnknown();
        }

        return mkOper(SortManager::INT_SORT, NODE_KIND::NT_STR_INDEXOF_REG, l, r);
    }

    // INTERVAL
    std::shared_ptr<DAGNode> Parser::mkMax(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for max", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (< a b c d) <=> (and (< a b) (< b c) (< c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in max, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in max", line_number);
                    return mkUnknown();
                }
            }
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_MAX, new_params);
    }
    std::shared_ptr<DAGNode> Parser::mkMin(const std::vector<std::shared_ptr<DAGNode>> &params){
        if(params.size() == 0){
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "Not enough parameters for min", line_number);
            return mkUnknown();
        }
        else if(params.size() == 1){
            return params[0];
        }
        std::shared_ptr<Sort> sort = getSort(params);

        std::vector<std::shared_ptr<DAGNode>> new_params;

        // pair-wise comparison: (< a b c d) <=> (and (< a b) (< b c) (< c d))
        for(size_t i=0;i<params.size() - 1;i++){
            if(params[i]->isErr()) return params[i];
            if(sort != nullptr && !params[i]->getSort()->isEqTo(sort)) {
                if(canExempt(params[i]->getSort(), sort)){
                    std::cerr << "Type mismatch in min, but now exempt for int/real"<<std::endl;
                }
                else{
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "Type mismatch in min", line_number);
                    return mkUnknown();
                }
            }
            new_params.emplace_back(params[i]);
        }

        return mkOper(sort, NODE_KIND::NT_MIN, new_params);
    }

    // negate an atom
    std::shared_ptr<DAGNode> Parser::negateComp(std::shared_ptr<DAGNode> atom){
        if(atom->isErr()) return atom;

        if(atom->isEq()){
            return mkDistinct(atom->getChildren());
        }
        else if(atom->isDistinct()){
            return mkEq(atom->getChildren());
        }

        // negate an arithmetic atom
        if(atom->isArithComp()){
            // less than
            if(atom->isLt()){
                return mkGe(atom->getChild(0), atom->getChild(1));
            }
            // less than or equal
            else if(atom->isLe()){
                return mkGt(atom->getChild(0), atom->getChild(1));
            }
            // greater than
            else if(atom->isGt()){
                return mkLe(atom->getChild(0), atom->getChild(1));
            }
            // greater than or equal
            else if(atom->isGe()){
                return mkLt(atom->getChild(0), atom->getChild(1));
            }
            else{
                condAssert(false, "negateComp: unknown arithmetic comparison operator");
            }
        }

        // negate a bitvector atom
        if(atom->isBVCompOp()){
            if(atom->isBVUlt()){
                return mkBvUge(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUle()){
                return mkBvUgt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUgt()){
                return mkBvUle(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUge()){
                return mkBvUlt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUlt()){
                return mkBvUge(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUle()){
                return mkBvUgt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUgt()){
                return mkBvUle(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVUge()){
                return mkBvUlt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVSlt()){
                return mkBvSge(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVSle()){
                return mkBvSgt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVSgt()){
                return mkBvSle(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isBVSge()){
                return mkBvSlt(atom->getChild(0), atom->getChild(1));
            }
            else{
                condAssert(false, "negateComp: unknown bitvector comparison operator");
            }
        }

        if(atom->isFPComp()){
            if(atom->isFPEq()){
                return mkFpNe(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isFPGt()){
                return mkFpLe(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isFPLt()){
                return mkFpGe(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isFPGe()){
                return mkFpLt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isFPLe()){
                return mkFpGt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isFPNe()){
                return mkFpEq(atom->getChild(0), atom->getChild(1));
            }
            else{
                condAssert(false, "negateComp: unknown floating-point comparison operator");
            }
        }

        if(atom->isStrComp()){
            if(atom->isStrLt()){
                return mkStrGe(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isStrLe()){
                return mkStrGt(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isStrGt()){
                return mkStrLe(atom->getChild(0), atom->getChild(1));
            }
            else if(atom->isStrGe()){
                return mkStrLt(atom->getChild(0), atom->getChild(1));
            }
            else{
                condAssert(false, "negateComp: unknown string comparison operator");
            }
        }

        // for other types of atoms, use the general negation operation
        return mkNot(atom);
    }

    std::shared_ptr<DAGNode> Parser::flipComp(std::shared_ptr<DAGNode> atom){
        if(atom->isErr()) return atom;

        if(atom->isEq() || atom->isDistinct()){
            return atom;
        }

        // negate an arithmetic atom
        if(atom->isArithComp()){
            return mkOper(SortManager::BOOL_SORT, atom->getKind(), {atom->getChild(1), atom->getChild(0)});
        }

        // negate a bitvector atom
        if(atom->isBVCompOp()){
            return mkOper(SortManager::BOOL_SORT, atom->getKind(), {atom->getChild(1), atom->getChild(0)});
        }

        if(atom->isFPComp()){
            return mkOper(SortManager::BOOL_SORT, atom->getKind(), {atom->getChild(1), atom->getChild(0)});
        }

        if(atom->isStrComp()){
            return mkOper(SortManager::BOOL_SORT, atom->getKind(), {atom->getChild(1), atom->getChild(0)});
        }

        // for other types of atoms, use the general negation operation
        return atom;
    }

    int Parser::getArity(NODE_KIND k) const{
        switch(k){
            // zero-ary
            case NODE_KIND::NT_NULL:
            case NODE_KIND::NT_CONST:
            case NODE_KIND::NT_VAR:
            case NODE_KIND::NT_TEMP_VAR:
            case NODE_KIND::NT_CONST_TRUE:
            case NODE_KIND::NT_CONST_FALSE:
            case NODE_KIND::NT_CONST_PI:
            case NODE_KIND::NT_CONST_E:
            case NODE_KIND::NT_INFINITY:
            case NODE_KIND::NT_POS_INFINITY:
            case NODE_KIND::NT_NEG_INFINITY:
            case NODE_KIND::NT_NAN:
            case NODE_KIND::NT_EPSILON:
            case NODE_KIND::NT_POS_EPSILON:
            case NODE_KIND::NT_NEG_EPSILON:
            case NODE_KIND::NT_REG_NONE:
            case NODE_KIND::NT_REG_ALL:
            case NODE_KIND::NT_REG_ALLCHAR:
            case NODE_KIND::NT_QUANT_VAR:
                return 0;
            
            // unary
            case NODE_KIND::NT_CONST_ARRAY:
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_NEG:
            case NODE_KIND::NT_ABS:
            case NODE_KIND::NT_SQRT:
            case NODE_KIND::NT_SAFESQRT:
            case NODE_KIND::NT_CEIL:
            case NODE_KIND::NT_FLOOR:
            case NODE_KIND::NT_ROUND:
            case NODE_KIND::NT_EXP:
            case NODE_KIND::NT_LN:
            case NODE_KIND::NT_LG:
            case NODE_KIND::NT_LB:
            case NODE_KIND::NT_SIN:
            case NODE_KIND::NT_COS:
            case NODE_KIND::NT_SEC:
            case NODE_KIND::NT_CSC:
            case NODE_KIND::NT_TAN:
            case NODE_KIND::NT_COT:
            case NODE_KIND::NT_ASIN:
            case NODE_KIND::NT_ACOS:
            case NODE_KIND::NT_ASEC:
            case NODE_KIND::NT_ACSC:
            case NODE_KIND::NT_ATAN:
            case NODE_KIND::NT_ACOT:
            case NODE_KIND::NT_SINH:
            case NODE_KIND::NT_COSH:
            case NODE_KIND::NT_TANH:
            case NODE_KIND::NT_SECH:
            case NODE_KIND::NT_CSCH:
            case NODE_KIND::NT_COTH:
            case NODE_KIND::NT_ASINH:
            case NODE_KIND::NT_ACOSH:
            case NODE_KIND::NT_ATANH:
            case NODE_KIND::NT_ASECH:
            case NODE_KIND::NT_ACSCH:
            case NODE_KIND::NT_ACOTH:
            case NODE_KIND::NT_TO_INT:
            case NODE_KIND::NT_TO_REAL:
            case NODE_KIND::NT_IS_INT:
            case NODE_KIND::NT_IS_PRIME:
            case NODE_KIND::NT_IS_EVEN:
            case NODE_KIND::NT_IS_ODD:
            case NODE_KIND::NT_FACT:
            case NODE_KIND::NT_BV_NOT:
            case NODE_KIND::NT_BV_NEG:
            case NODE_KIND::NT_BV_NEGO:
            case NODE_KIND::NT_FP_ABS:
            case NODE_KIND::NT_FP_NEG:
            case NODE_KIND::NT_FP_SQRT:
            case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
            case NODE_KIND::NT_FP_IS_NORMAL:
            case NODE_KIND::NT_FP_IS_SUBNORMAL:
            case NODE_KIND::NT_FP_IS_ZERO:
            case NODE_KIND::NT_FP_IS_INF:
            case NODE_KIND::NT_FP_IS_NAN:
            case NODE_KIND::NT_FP_IS_NEG:
            case NODE_KIND::NT_FP_IS_POS:
            case NODE_KIND::NT_FP_TO_UBV:
            case NODE_KIND::NT_FP_TO_SBV:
            case NODE_KIND::NT_FP_TO_REAL:
            case NODE_KIND::NT_STR_LEN:
            case NODE_KIND::NT_STR_TO_LOWER:
            case NODE_KIND::NT_STR_TO_UPPER:
            case NODE_KIND::NT_STR_REV:
            case NODE_KIND::NT_STR_IS_DIGIT:
            case NODE_KIND::NT_STR_FROM_INT:
            case NODE_KIND::NT_STR_TO_INT:
            case NODE_KIND::NT_STR_TO_REG:
            case NODE_KIND::NT_STR_TO_CODE:
            case NODE_KIND::NT_STR_FROM_CODE:
            case NODE_KIND::NT_REG_STAR:
            case NODE_KIND::NT_REG_PLUS:
            case NODE_KIND::NT_REG_OPT:
            case NODE_KIND::NT_REG_COMPLEMENT:
            case NODE_KIND::NT_BV_TO_NAT:
            case NODE_KIND::NT_BV_TO_INT:
            case NODE_KIND::NT_POW2:
                return 1;

            // binary
            case NODE_KIND::NT_POW:
            case NODE_KIND::NT_DIV_INT:
            case NODE_KIND::NT_DIV_REAL:
            case NODE_KIND::NT_MOD:
            case NODE_KIND::NT_LOG:
            case NODE_KIND::NT_ATAN2:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_IS_DIVISIBLE:
            case NODE_KIND::NT_GCD:
            case NODE_KIND::NT_LCM:
            case NODE_KIND::NT_BV_UDIV:
            case NODE_KIND::NT_BV_SDIV:
            case NODE_KIND::NT_BV_UREM:
            case NODE_KIND::NT_BV_SREM:
            case NODE_KIND::NT_BV_UMOD:
            case NODE_KIND::NT_BV_SMOD:
            case NODE_KIND::NT_BV_SDIVO:
            case NODE_KIND::NT_BV_UDIVO:
            case NODE_KIND::NT_BV_SREMO:
            case NODE_KIND::NT_BV_UREMO:
            case NODE_KIND::NT_BV_SMODO:
            case NODE_KIND::NT_BV_UMODO:
            case NODE_KIND::NT_BV_SHL:
            case NODE_KIND::NT_BV_LSHR:
            case NODE_KIND::NT_BV_ASHR:
            case NODE_KIND::NT_BV_COMP:
            case NODE_KIND::NT_BV_ULT:
            case NODE_KIND::NT_BV_ULE:
            case NODE_KIND::NT_BV_UGT:
            case NODE_KIND::NT_BV_UGE:
            case NODE_KIND::NT_BV_SLT:
            case NODE_KIND::NT_BV_SLE:
            case NODE_KIND::NT_BV_SGT:
            case NODE_KIND::NT_BV_SGE:
            case NODE_KIND::NT_NAT_TO_BV:
            case NODE_KIND::NT_INT_TO_BV:
            case NODE_KIND::NT_FP_DIV:
            case NODE_KIND::NT_FP_REM:
            case NODE_KIND::NT_FP_LE:
            case NODE_KIND::NT_FP_LT:
            case NODE_KIND::NT_FP_GE:
            case NODE_KIND::NT_FP_GT:
            case NODE_KIND::NT_FP_EQ:
            case NODE_KIND::NT_FP_NE:
            case NODE_KIND::NT_SELECT:
            case NODE_KIND::NT_STR_PREFIXOF:
            case NODE_KIND::NT_STR_SUFFIXOF:
            case NODE_KIND::NT_STR_CHARAT:
            case NODE_KIND::NT_STR_SPLIT:
            case NODE_KIND::NT_STR_LT:
            case NODE_KIND::NT_STR_LE:
            case NODE_KIND::NT_STR_GT:
            case NODE_KIND::NT_STR_GE:
            case NODE_KIND::NT_STR_IN_REG:
            case NODE_KIND::NT_STR_CONTAINS:
            case NODE_KIND::NT_STR_NUM_SPLITS_RE:
            case NODE_KIND::NT_REG_RANGE:
            case NODE_KIND::NT_REG_REPEAT:
            case NODE_KIND::NT_BV_REPEAT:
            case NODE_KIND::NT_BV_ZERO_EXT:
            case NODE_KIND::NT_BV_SIGN_EXT:
            case NODE_KIND::NT_BV_ROTATE_LEFT:
            case NODE_KIND::NT_BV_ROTATE_RIGHT:
                return 2;

            // ternary
            case NODE_KIND::NT_ITE:
            case NODE_KIND::NT_FP_FMA:
            case NODE_KIND::NT_STORE:
            case NODE_KIND::NT_STR_SUBSTR:
            case NODE_KIND::NT_STR_INDEXOF:
            case NODE_KIND::NT_STR_UPDATE:
            case NODE_KIND::NT_STR_REPLACE:
            case NODE_KIND::NT_STR_REPLACE_ALL:
            case NODE_KIND::NT_STR_SPLIT_AT:
            case NODE_KIND::NT_STR_SPLIT_REST:
            case NODE_KIND::NT_STR_SPLIT_AT_RE:
            case NODE_KIND::NT_STR_SPLIT_REST_RE:
            case NODE_KIND::NT_STR_REPLACE_REG:
            case NODE_KIND::NT_STR_REPLACE_REG_ALL:
            case NODE_KIND::NT_STR_INDEXOF_REG:
            case NODE_KIND::NT_REG_LOOP:
            case NODE_KIND::NT_BV_EXTRACT:
                return 3;

            // 4-ary
            case NODE_KIND::NT_FP_TO_FP:
                return 4;

            // n-ary
            case NODE_KIND::NT_EQ:
            case NODE_KIND::NT_EQ_BOOL:
            case NODE_KIND::NT_EQ_OTHER:
            case NODE_KIND::NT_DISTINCT:
            case NODE_KIND::NT_DISTINCT_BOOL:
            case NODE_KIND::NT_DISTINCT_OTHER:
            case NODE_KIND::NT_AND:
            case NODE_KIND::NT_OR:
            case NODE_KIND::NT_IMPLIES:
            case NODE_KIND::NT_XOR:
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_IAND:
            case NODE_KIND::NT_SUB:
            case NODE_KIND::NT_BV_AND:
            case NODE_KIND::NT_BV_OR:
            case NODE_KIND::NT_BV_XOR:
            case NODE_KIND::NT_BV_NAND:
            case NODE_KIND::NT_BV_NOR:
            case NODE_KIND::NT_BV_XNOR:
            case NODE_KIND::NT_BV_ADD:
            case NODE_KIND::NT_BV_SUB:
            case NODE_KIND::NT_BV_MUL:
            case NODE_KIND::NT_BV_SADDO:
            case NODE_KIND::NT_BV_UADDO:
            case NODE_KIND::NT_BV_SMULO:
            case NODE_KIND::NT_BV_UMULO:
            case NODE_KIND::NT_BV_CONCAT:
            case NODE_KIND::NT_FP_ADD:
            case NODE_KIND::NT_FP_SUB:
            case NODE_KIND::NT_FP_MUL:
            case NODE_KIND::NT_FP_MIN:
            case NODE_KIND::NT_FP_MAX:
            case NODE_KIND::NT_STR_CONCAT:
            case NODE_KIND::NT_REG_CONCAT:
            case NODE_KIND::NT_REG_UNION:
            case NODE_KIND::NT_REG_INTER:
            case NODE_KIND::NT_REG_DIFF:
            case NODE_KIND::NT_FORALL:
            case NODE_KIND::NT_EXISTS:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:
                return -1;

            default:
                return -1;
        }
    }

    // ROOT OBJECT
    std::shared_ptr<DAGNode> Parser::mkRootObj(std::shared_ptr<DAGNode> expr, int index) {
        if(expr->isErr()) return expr;
        
        // Create index as integer constant
        std::shared_ptr<DAGNode> index_node = mkConstInt(index);
        
        // Create root-obj node with real sort
        std::shared_ptr<Sort> sort = SortManager::REAL_SORT;
        std::string name = "root-obj(" + toString(expr) + "," + std::to_string(index) + ")";
        std::vector<std::shared_ptr<DAGNode>> children = {expr, index_node};
        
        return node_manager->createNode(sort, NODE_KIND::NT_ROOT_OBJ, name, children);
    }
}
