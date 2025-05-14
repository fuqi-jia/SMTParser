/* -*- Header -*-
 *
 * An SMT/OMT Parser
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

#ifndef PARSER_HEADER
#define PARSER_HEADER

#include "dag.h"
#include "util.h"
#include "options.h"
#include "objective.h"

#include <boost/unordered_set.hpp>

namespace SMTLIBParser{
    enum class SCAN_MODE {
        SM_COMMON,
        SM_SYMBOL,
        SM_COMP_SYM,
        SM_COMMENT,
        SM_STRING
    };

    enum class KEYWORD{
        KW_ID, KW_WEIGHT, KW_COMP, KW_EPSILON, KW_M, KW_OPT_KIND, KW_NULL
    };

    enum class CMD_TYPE {
        CT_UNKNOWN, CT_EOF,
        // COMMANDS
        CT_ASSERT, CT_CHECK_SAT, CT_CHECK_SAT_ASSUMING,
        CT_DECLARE_CONST, CT_DECLARE_FUN, CT_DECLARE_SORT,
        CT_DEFINE_FUN, CT_DEFINE_FUN_REC, CT_DEFINE_FUNS_REC, CT_DEFINE_SORT,
        CT_ECHO, CT_EXIT,
        CT_GET_ASSERTIONS, CT_GET_ASSIGNMENT, CT_GET_INFO,
        CT_GET_MODEL, CT_GET_OPTION, CT_GET_PROOF,
        CT_GET_UNSAT_ASSUMPTIONS, CT_GET_UNSAT_CORE, CT_GET_VALUE,
        CT_POP, CT_PUSH, CT_RESET, CT_RESET_ASSERTIONS,
        CT_SET_INFO, CT_SET_LOGIC, CT_SET_OPTION,
        // QUANTIFIER
        CT_EXISTS, CT_FORALL,
        // OPTIMIZATION COMMANDS
        CT_GET_OBJECTIVES, CT_ASSERT_SOFT, 
        CT_DEFINE_OBJ, CT_DEFINE_MIN_OBJ, CT_DEFINE_MAX_OBJ,
        CT_MINIMIZE, CT_MAXIMIZE, CT_LEX_OPTIMIZE, CT_PARETO_OPTIMIZE, CT_BOX_OPTIMIZE, CT_MINMAX, CT_MAXMIN, CT_MAXSAT, CT_MINSAT, CT_OPTIMIZE
        // CT_LEX_MAXIMIZE, CT_PARETO_MINIMIZE, CT_PARETO_MAXIMIZE, 
        // CT_BOX_MINIMIZE, CT_BOX_MAXIMIZE, CT_MINMAX, CT_MAXMIN
    };

    enum class ERROR_TYPE {
        ERR_UNEXP_EOF,
        ERR_SYM_MIS,
        ERR_UNKWN_SYM,
        ERR_PARAM_MIS,
        ERR_PARAM_NBOOL,
        ERR_PARAM_NNUM,
        ERR_PARAM_NSAME,
        ERR_LOGIC,
        ERR_MUL_DECL,
        ERR_MUL_DEF,
        ERR_ZERO_DIVISOR,
        ERR_FUN_LOCAL_VAR,
        ERR_ARI_MIS,
        ERR_TYPE_MIS,
        ERR_NEG_PARAM
    };


    /*
    Parser
    */

    // NOTE: only non-incremental mode
    class Parser {
    private:

        // attributes

        // vars for parser
        char 			                        *buffer;
        unsigned long	                        buflen;
        char			                        *bufptr;
        size_t 	                                line_number;
        SCAN_MODE 		                        scan_mode;

        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                let_key_map; // local variables, no need to hash store
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                fun_key_map; 
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                fun_var_map; // variables are not the same, no need to hash store
        boost::unordered_map<std::string, std::shared_ptr<Sort>>
                                                sort_key_map;
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>>
                                                quant_var_map;
        std::vector<std::shared_ptr<DAGNode>>   static_functions; // static functions without substitution

        // FOL binding

        // error node
        std::shared_ptr<DAGNode>	                    err_node;
        // false node
        std::shared_ptr<DAGNode>			            false_node;
        // true node
        std::shared_ptr<DAGNode>			            true_node;
        // node list
        std::vector<std::shared_ptr<DAGNode>>           node_list;
        // variable name list
        boost::unordered_map<std::string, size_t>       var_names;
        // const node
        boost::unordered_map<std::string, size_t>       constants;
        std::vector<std::string>                        function_names;
        // global options
        std::shared_ptr<GlobalOptions>                  options;
        // hash value list
        boost::unordered_map<std::shared_ptr<DAGNode>, size_t, NodeHash, NodeEqual>
                                                        complex_node_map;
        // (define-objective name single_opt)
        boost::unordered_map<std::string, std::shared_ptr<Objective>> 
                                                        objective_map;
        
    public:
        std::vector<std::shared_ptr<DAGNode>>               assertions;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> 
                                                            assertion_groups;
        std::vector<std::vector<std::shared_ptr<DAGNode>>>  assumptions;
        std::vector<std::shared_ptr<DAGNode>>               soft_assertions;
        std::vector<std::shared_ptr<DAGNode>>               soft_weights;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> 
                                                            soft_assertion_groups;
        std::vector<std::shared_ptr<Objective>>             objectives;


    public:

        //methods
        Parser(const std::string& filename);
        Parser();
        ~Parser();
        bool parse(const std::string& filename);

        // to solver
        std::vector<std::shared_ptr<DAGNode>> getAssertions() const;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> getGroupedAssertions() const;
        std::vector<std::vector<std::shared_ptr<DAGNode>>> getAssumptions() const;
        std::vector<std::shared_ptr<DAGNode>> getSoftAssertions() const;
        std::vector<std::shared_ptr<DAGNode>> getSoftWeights() const;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> getGroupedSoftAssertions() const;
        std::vector<std::shared_ptr<Objective>> getObjectives() const;
        std::shared_ptr<GlobalOptions> getOptions() const;
        std::vector<std::shared_ptr<DAGNode>> getVariables() const;
        std::vector<std::shared_ptr<DAGNode>> getFunctions() const;

        // get sort
        std::shared_ptr<Sort> getSort(const std::vector<std::shared_ptr<DAGNode>>& params);
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> param);
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> m);

        // mk oper 
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p);
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p);
        // mk function
        std::shared_ptr<DAGNode> mkFuncDec(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);
        std::shared_ptr<DAGNode> mkFuncDef(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body);
        // mk sort
        std::shared_ptr<Sort> mkSortDec(const std::string &name, const size_t &arity);
        // mk true/false
        std::shared_ptr<DAGNode>	mkTrue(); // true
        std::shared_ptr<DAGNode>	mkFalse(); // false
        // CORE OPERATORS
        std::shared_ptr<DAGNode> mkEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        std::shared_ptr<DAGNode> mkEq(const std::vector<std::shared_ptr<DAGNode>>& params); // l = r = ... 
        std::shared_ptr<DAGNode> mkDistinct(const std::vector<std::shared_ptr<DAGNode>> &params); // l != r != ...
        std::shared_ptr<DAGNode> mkDistinct(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l != r
        // CONST
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const std::string &v); // CONST
        std::shared_ptr<DAGNode> mkConstBool(const std::string &v); // CONST_BOOL
        std::shared_ptr<DAGNode> mkConstRat(const Rational &v); // CONST_RAN
        std::shared_ptr<DAGNode> mkConstRat(const Rational &l, const Rational &r); // CONST_RAN
        std::shared_ptr<DAGNode> mkConstRat(const Integer &l, const Integer &r); // CONST_RAN
        std::shared_ptr<DAGNode> mkConstInt(const std::string &v); // CONST_INT
        std::shared_ptr<DAGNode> mkConstInt(const Integer &v); // CONST_INT
        std::shared_ptr<DAGNode> mkConstReal(const std::string &v); // CONST_REAL
        std::shared_ptr<DAGNode> mkConstReal(const Real &v); // CONST_REAL
        std::shared_ptr<DAGNode> mkConstStr(const std::string &v); // CONST_Str
        std::shared_ptr<DAGNode> mkConstBv(const std::string &v, const size_t& width); // CONST_BV
        std::shared_ptr<DAGNode> mkConstFp(const std::string &v, const size_t& e, const size_t& s); // CONST_FP
        std::shared_ptr<DAGNode> mkConstReg(const std::string &v); // CONST_REG
        // VAR
        // TODO ...
        std::shared_ptr<DAGNode> mkVar(const std::shared_ptr<Sort>& sort, const std::string &name); // VAR
        std::shared_ptr<DAGNode> mkVarBool(const std::string &name); // VAR_BOOL
        std::shared_ptr<DAGNode> mkVarInt(const std::string &name); // VAR_INT
        std::shared_ptr<DAGNode> mkVarReal(const std::string &name); // VAR_REAL
        std::shared_ptr<DAGNode> mkVarBv(const std::string &name, const size_t& width); // VAR_BV
        std::shared_ptr<DAGNode> mkVarFp(const std::string &name, const size_t& e, const size_t& s); // VAR_FP
        std::shared_ptr<DAGNode> mkVarStr(const std::string &name); // VAR_STR
        std::shared_ptr<DAGNode> mkVarReg(const std::string &name); // VAR_REG
        std::shared_ptr<DAGNode> mkFunParamVar(std::shared_ptr<Sort> sort, const std::string &name); // FUN_PARAM_VAR
        // ARRAY
        std::shared_ptr<DAGNode> mkArray(const std::string &name, std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem); // ARRAY
        // BOOLEAN
        std::shared_ptr<DAGNode> mkNot(std::shared_ptr<DAGNode> param);
        std::shared_ptr<DAGNode> mkAnd(const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode> mkOr(const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode> mkImplies(const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode> mkXor(const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode> mkIte(std::shared_ptr<DAGNode> cond, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        std::shared_ptr<DAGNode> mkIte(const std::vector<std::shared_ptr<DAGNode>> &params);
        // ARITHMATIC COMMON OPERATORS
        std::shared_ptr<DAGNode> mkAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        std::shared_ptr<DAGNode> mkIand(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ... 
        std::shared_ptr<DAGNode> mkPow2(std::shared_ptr<DAGNode> param); // 2^param
        std::shared_ptr<DAGNode> mkPow(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l^r
        std::shared_ptr<DAGNode> mkSub(const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode> mkNeg(std::shared_ptr<DAGNode> param); // -param
        std::shared_ptr<DAGNode> mkDivInt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkDivReal(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkMod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkAbs(std::shared_ptr<DAGNode> param); // |param|
        std::shared_ptr<DAGNode> mkSqrt(std::shared_ptr<DAGNode> param); // sqrt(param)
        std::shared_ptr<DAGNode> mkSafeSqrt(std::shared_ptr<DAGNode> param); // safesqrt(param)
        std::shared_ptr<DAGNode> mkCeil(std::shared_ptr<DAGNode> param); // ceil(param)
        std::shared_ptr<DAGNode> mkFloor(std::shared_ptr<DAGNode> param); // floor(param)
        std::shared_ptr<DAGNode> mkRound(std::shared_ptr<DAGNode> param); // round(param)
        // TRANSCENDENTAL ARITHMATIC
        std::shared_ptr<DAGNode> mkExp(std::shared_ptr<DAGNode> param); // exp(param)
        std::shared_ptr<DAGNode> mkLn(std::shared_ptr<DAGNode> param); // ln(param)
        std::shared_ptr<DAGNode> mkLg(std::shared_ptr<DAGNode> param); // lg(param)
        std::shared_ptr<DAGNode> mkLb(std::shared_ptr<DAGNode> param); // lb(param)
        std::shared_ptr<DAGNode> mkLog(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // log_l(r)
        std::shared_ptr<DAGNode> mkSin(std::shared_ptr<DAGNode> param); // sin(param)
        std::shared_ptr<DAGNode> mkCos(std::shared_ptr<DAGNode> param); // cos(param)
        std::shared_ptr<DAGNode> mkSec(std::shared_ptr<DAGNode> param); // sec(param)
        std::shared_ptr<DAGNode> mkCsc(std::shared_ptr<DAGNode> param); // csc(param)
        std::shared_ptr<DAGNode> mkTan(std::shared_ptr<DAGNode> param); // tan(param)
        std::shared_ptr<DAGNode> mkCot(std::shared_ptr<DAGNode> param); // cot(param)
        std::shared_ptr<DAGNode> mkAsin(std::shared_ptr<DAGNode> param); // asin(param)
        std::shared_ptr<DAGNode> mkAcos(std::shared_ptr<DAGNode> param); // acos(param)
        std::shared_ptr<DAGNode> mkAsec(std::shared_ptr<DAGNode> param); // asec(param)
        std::shared_ptr<DAGNode> mkAcsc(std::shared_ptr<DAGNode> param); // acsc(param)
        std::shared_ptr<DAGNode> mkAtan(std::shared_ptr<DAGNode> param); // atan(param)
        std::shared_ptr<DAGNode> mkAcot(std::shared_ptr<DAGNode> param); // acot(param)
        std::shared_ptr<DAGNode> mkSinh(std::shared_ptr<DAGNode> param); // sinh(param)
        std::shared_ptr<DAGNode> mkCosh(std::shared_ptr<DAGNode> param); // cosh(param)
        std::shared_ptr<DAGNode> mkTanh(std::shared_ptr<DAGNode> param); // tanh(param)
        std::shared_ptr<DAGNode> mkSech(std::shared_ptr<DAGNode> param); // sech(param)
        std::shared_ptr<DAGNode> mkCsch(std::shared_ptr<DAGNode> param); // csch(param)
        std::shared_ptr<DAGNode> mkCoth(std::shared_ptr<DAGNode> param); // coth(param)
        std::shared_ptr<DAGNode> mkAsinh(std::shared_ptr<DAGNode> param); // asinh(param)
        std::shared_ptr<DAGNode> mkAcosh(std::shared_ptr<DAGNode> param); // acosh(param)
        std::shared_ptr<DAGNode> mkAtanh(std::shared_ptr<DAGNode> param); // atanh(param)
        std::shared_ptr<DAGNode> mkAsech(std::shared_ptr<DAGNode> param); // asech(param)
        std::shared_ptr<DAGNode> mkAcsch(std::shared_ptr<DAGNode> param); // acsch(param)
        std::shared_ptr<DAGNode> mkAcoth(std::shared_ptr<DAGNode> param); // acoth(param)
        std::shared_ptr<DAGNode> mkAtan2(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        // ARITHMATIC COMP
        std::shared_ptr<DAGNode> mkLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkLe(const std::vector<std::shared_ptr<DAGNode>>& params); // l <= r
        std::shared_ptr<DAGNode> mkLt(const std::vector<std::shared_ptr<DAGNode>>& params); // l < r
        std::shared_ptr<DAGNode> mkGe(const std::vector<std::shared_ptr<DAGNode>>& params); // l >= r
        std::shared_ptr<DAGNode> mkGt(const std::vector<std::shared_ptr<DAGNode>>& params); // l > r
        // ARITHMATIC CONVERSION
        std::shared_ptr<DAGNode> mkToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkToReal(std::shared_ptr<DAGNode> param); // to_real(param)
        // ARITHMATIC PROPERTIES
        std::shared_ptr<DAGNode> mkIsInt(std::shared_ptr<DAGNode> param); // is_int(param)
        std::shared_ptr<DAGNode> mkIsDivisible(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // is_divisible(l, r)
        std::shared_ptr<DAGNode> mkIsPrime(std::shared_ptr<DAGNode> param); // is_prime(param)
        std::shared_ptr<DAGNode> mkIsEven(std::shared_ptr<DAGNode> param); // is_even(param)
        std::shared_ptr<DAGNode> mkIsOdd(std::shared_ptr<DAGNode> param); // is_odd(param)
        // ARITHMATIC CONSTANTS
        std::shared_ptr<DAGNode> mkPi(); // pi
        std::shared_ptr<DAGNode> mkE(); // e
        std::shared_ptr<DAGNode> mkInfinity(); // infinity
        std::shared_ptr<DAGNode> mkNan(); // nan
        std::shared_ptr<DAGNode> mkEpsilon(); // epsilon
        // ARITHMATIC FUNCTIONS
        // std::shared_ptr<DAGNode> mkSum(const std::vector<std::shared_ptr<DAGNode>> &params); // \Sigma params
        // std::shared_ptr<DAGNode> mkProd(const std::vector<std::shared_ptr<DAGNode>> &params); // \Prod params
        std::shared_ptr<DAGNode> mkGcd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // gcd(l, r)
        std::shared_ptr<DAGNode> mkLcm(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // lcm(l, r)
        std::shared_ptr<DAGNode> mkFact(std::shared_ptr<DAGNode> param); // factorial(param)
        // BITVECTOR COMMON OPERATORS
        std::shared_ptr<DAGNode> mkBvNot(std::shared_ptr<DAGNode> param); // ~param
        std::shared_ptr<DAGNode> mkBvAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l & r
        std::shared_ptr<DAGNode> mkBvAnd(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ...
        std::shared_ptr<DAGNode> mkBvOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l | r
        std::shared_ptr<DAGNode> mkBvOr(const std::vector<std::shared_ptr<DAGNode>> &params); // l | r | ...
        std::shared_ptr<DAGNode> mkBvXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l ^ r
        std::shared_ptr<DAGNode> mkBvXor(const std::vector<std::shared_ptr<DAGNode>> &params); // l ^ r ^ ...
        std::shared_ptr<DAGNode> mkBvNand(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l & r)
        std::shared_ptr<DAGNode> mkBvNand(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l & r & ...)
        std::shared_ptr<DAGNode> mkBvNor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l | r)
        std::shared_ptr<DAGNode> mkBvNor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l | r | ...)
        std::shared_ptr<DAGNode> mkBvXnor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l ^ r)
        std::shared_ptr<DAGNode> mkBvComp(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        std::shared_ptr<DAGNode> mkBvXnor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l ^ r ^ ...)
        std::shared_ptr<DAGNode> mkBvNeg(std::shared_ptr<DAGNode> param); // -param
        std::shared_ptr<DAGNode> mkBvAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l + r
        std::shared_ptr<DAGNode> mkBvAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkBvSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l - r
        std::shared_ptr<DAGNode> mkBvSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkBvMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        std::shared_ptr<DAGNode> mkBvMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        std::shared_ptr<DAGNode> mkBvUdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkBvUrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvSdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkBvSrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvSmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvShl(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l << r
        std::shared_ptr<DAGNode> mkBvLshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        std::shared_ptr<DAGNode> mkBvAshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        std::shared_ptr<DAGNode> mkBvConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // l ++ r ++ ...
        std::shared_ptr<DAGNode> mkBvExtract(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l[r:s]
        std::shared_ptr<DAGNode> mkBvRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        std::shared_ptr<DAGNode> mkBvZeroExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l zero_extend r
        std::shared_ptr<DAGNode> mkBvSignExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l sign_extend r
        std::shared_ptr<DAGNode> mkBvRotateLeft(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <<< r
        std::shared_ptr<DAGNode> mkBvRotateRight(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >>> r
        // BITVECTOR COMP
        std::shared_ptr<DAGNode> mkBvUlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkBvUle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkBvUgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkBvUge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkBvSlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkBvSle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkBvSgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkBvSge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        // BITVECTOR CONVERSION
        std::shared_ptr<DAGNode> mkBvToNat(std::shared_ptr<DAGNode> param); // to_nat(param)
        std::shared_ptr<DAGNode> mkNatToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)
        std::shared_ptr<DAGNode> mkBvToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkIntToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)
        // FLOATING POINT COMMON OPERATORS
        std::shared_ptr<DAGNode> mkFpAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkFpSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkFpMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        std::shared_ptr<DAGNode> mkFpDiv(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        std::shared_ptr<DAGNode> mkFpAbs(std::shared_ptr<DAGNode> param); // |param|
        std::shared_ptr<DAGNode> mkFpNeg(std::shared_ptr<DAGNode> param); // -param
        std::shared_ptr<DAGNode> mkFpRem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkFpFma(const std::vector<std::shared_ptr<DAGNode>> &params); // fma(a, b, c) = a * b + c
        std::shared_ptr<DAGNode> mkFpSqrt(std::shared_ptr<DAGNode> param); // sqrt(param)
        std::shared_ptr<DAGNode> mkFpRoundToIntegral(std::shared_ptr<DAGNode> param); // round_to_integral(param)
        std::shared_ptr<DAGNode> mkFpMin(const std::vector<std::shared_ptr<DAGNode>> &params); // min(params)
        std::shared_ptr<DAGNode> mkFpMax(const std::vector<std::shared_ptr<DAGNode>> &params); // max(params)
        // FLOATING POINT COMP
        std::shared_ptr<DAGNode> mkFpLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkFpLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkFpGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkFpGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkFpEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        // FLOATING POINT CONVERSION
        std::shared_ptr<DAGNode> mkFpToUbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_ubv(param, size)
        std::shared_ptr<DAGNode> mkFpToSbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_sbv(param, size)
        std::shared_ptr<DAGNode> mkFpToReal(std::shared_ptr<DAGNode> param); // to_real(param)
        std::shared_ptr<DAGNode> mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> param); // to_fp(eb, sb, param)
        // FLOATING POINT PROPERTIES
        std::shared_ptr<DAGNode> mkFpIsNormal(std::shared_ptr<DAGNode> param); // is_normal(param)
        std::shared_ptr<DAGNode> mkFpIsSubnormal(std::shared_ptr<DAGNode> param); // is_subnormal(param)
        std::shared_ptr<DAGNode> mkFpIsZero(std::shared_ptr<DAGNode> param); // is_zero(param)
        std::shared_ptr<DAGNode> mkFpIsInf(std::shared_ptr<DAGNode> param); // is_inf(param)
        std::shared_ptr<DAGNode> mkFpIsNan(std::shared_ptr<DAGNode> param); // is_nan(param)
        std::shared_ptr<DAGNode> mkFpIsNeg(std::shared_ptr<DAGNode> param); // is_neg(param)
        std::shared_ptr<DAGNode> mkFpIsPos(std::shared_ptr<DAGNode> param); // is_pos(param)
        // ARRAY
        std::shared_ptr<DAGNode> mkSelect(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l[r]
        std::shared_ptr<DAGNode> mkStore(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // l[r] = v
        // STRINGS COMMON OPERATORS
        std::shared_ptr<DAGNode> mkStrLen(std::shared_ptr<DAGNode> param); // len(param)
        std::shared_ptr<DAGNode> mkStrConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // param1 + param2 + ...
        std::shared_ptr<DAGNode> mkStrSubstr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l.substr(r, s)
        std::shared_ptr<DAGNode> mkStrPrefixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // prefixof(l, r)
        std::shared_ptr<DAGNode> mkStrSuffixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // suffixof(l, r)
        std::shared_ptr<DAGNode> mkStrIndexof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // indexof(l, r, s)
        std::shared_ptr<DAGNode> mkStrCharat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // charat(l, r)
        std::shared_ptr<DAGNode> mkStrUpdate(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // update(l, r, v)
        std::shared_ptr<DAGNode> mkStrReplace(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace(l, r, v)
        std::shared_ptr<DAGNode> mkStrReplaceAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace_all(l, r, v)
        std::shared_ptr<DAGNode> mkStrToLower(std::shared_ptr<DAGNode> param); // to_lower(param)
        std::shared_ptr<DAGNode> mkStrToUpper(std::shared_ptr<DAGNode> param); // to_upper(param)
        std::shared_ptr<DAGNode> mkStrRev(std::shared_ptr<DAGNode> param); // rev(param)
        std::shared_ptr<DAGNode> mkStrSplit(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // split(l, r)
        // STRINGS COMP
        std::shared_ptr<DAGNode> mkStrLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkStrLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkStrGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkStrGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        // STRINGS PROPERTIES
        std::shared_ptr<DAGNode> mkStrInReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l in r
        std::shared_ptr<DAGNode> mkStrContains(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // contains(l, r)
        std::shared_ptr<DAGNode> mkStrIsDigit(std::shared_ptr<DAGNode> param); // is_digit(param)
        // STRINGS CONVERSION
        std::shared_ptr<DAGNode> mkStrFromInt(std::shared_ptr<DAGNode> param); // from_int(param)
        std::shared_ptr<DAGNode> mkStrToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkStrToReg(std::shared_ptr<DAGNode> param); // to_reg(param)
        std::shared_ptr<DAGNode> mkStrToCode(std::shared_ptr<DAGNode> param); // to_code(param) assci code
        std::shared_ptr<DAGNode> mkStrFromCode(std::shared_ptr<DAGNode> param); // from_code(param) assci code
        // STRINGS RE CONSTANTS
        std::shared_ptr<DAGNode> mkRegNone(); // none
        std::shared_ptr<DAGNode> mkRegAll(); // all
        std::shared_ptr<DAGNode> mkRegAllChar(); // allchar
        // STRINGS RE COMMON OPERATORS
        std::shared_ptr<DAGNode> mkRegConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkRegUnion(const std::vector<std::shared_ptr<DAGNode>> &params); // l | r | ...
        std::shared_ptr<DAGNode> mkRegInter(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ...
        std::shared_ptr<DAGNode> mkRegDiff(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkRegStar(std::shared_ptr<DAGNode> param); // param*
        std::shared_ptr<DAGNode> mkRegPlus(std::shared_ptr<DAGNode> param); // param+
        std::shared_ptr<DAGNode> mkRegOpt(std::shared_ptr<DAGNode> param); // param?
        std::shared_ptr<DAGNode> mkRegRange(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l..r
        std::shared_ptr<DAGNode> mkRegRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // re.^n reg
        std::shared_ptr<DAGNode> mkRegLoop(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l{r,s}
        std::shared_ptr<DAGNode> mkRegComplement(std::shared_ptr<DAGNode> param); // ~param
        // STRINGS RE FUNCTIONS
        std::shared_ptr<DAGNode> mkReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace(l, r, v)
        std::shared_ptr<DAGNode> mkReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace_all(l, r, v)
        std::shared_ptr<DAGNode> mkIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // indexof(l, r)
        // LET 
        std::shared_ptr<DAGNode> mkLet(const std::vector<std::shared_ptr<DAGNode>> &params); // let((key1, val1), (key2, val2), ...)
        // QUANTIFIERS
        std::shared_ptr<DAGNode> mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort);
        std::shared_ptr<DAGNode> mkForall(const std::vector<std::shared_ptr<DAGNode>> &params); // forall((var1, sort1), (var2, sort2), ..., body)
        std::shared_ptr<DAGNode> mkExists(const std::vector<std::shared_ptr<DAGNode>> &params); // exists((var1, sort1), (var2, sort2), ..., body)
        // FUNCTION
        std::shared_ptr<DAGNode> mkApplyFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params); // static apply function, only (f p1 p2 ... pn) without substitution
        

        // parse smt-lib2 file
        bool 	                 parseSmtlib2File(const std::string filename);
        // // // parse model file
        // void 	            parseModel(std::string filename, boost::unordered_map<std::string, vType>& recs);

        std::shared_ptr<Sort> mkSort(); // mk unique sort, TODO!!!! for example, bv, fp, and array

        // aux functions
        NODE_KIND getAddOp(std::shared_ptr<Sort> sort); // mk unique add 
        std::shared_ptr<DAGNode> getZero(std::shared_ptr<Sort> sort); // mk unique zero

        // parse optimization
        // single_opt = (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>]) 
        //            | (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])

        void                             parseAssertSoft();
        // (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>       parseMaximize();
        // (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>       parseMinimize();
        // (maxsat <expr> [:id])
        std::shared_ptr<Objective>       parseMaxsat();
        // (minsat <expr> [:id])
        std::shared_ptr<Objective>       parseMinsat();
        std::shared_ptr<Objective>       parseSingleObj(const OPT_KIND& opt_type);
        std::shared_ptr<Objective>       parseMultiObj(const OPT_KIND& opt_type);
        // (define-objective <symbol> signle_opt [:id <symbol>])
        std::shared_ptr<Objective>       parseDefObj();
        // (lex-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseLexOpt();
        // (pareto-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseParetoOpt();
        // (box-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseBoxOpt();
        // (minmax (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseMinmax();
        // (maxmin (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseMaxmin();
        // (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
        std::shared_ptr<Objective>       parseOptimize();
        KEYWORD                          attemptParseKeywords();

        
        // additional functions
        std::shared_ptr<DAGNode>            substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode>            substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited);
        // apply function
        std::shared_ptr<DAGNode>	        applyFun(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> & params);
        std::shared_ptr<DAGNode>	        applyFunPostOrder(std::shared_ptr<DAGNode> node, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params);
        // negate an atom
        std::shared_ptr<DAGNode>	        negateAtom(std::shared_ptr<DAGNode> atom);

    private:
        // parse smt-lib2 file
        std::string	                        getSymbol();
        void 		                        scanToNextSymbol();
        void		                        parseLpar();
        void 		                        parseRpar();
        void		                        skipToRpar();
        std::string                         peekSymbol();


        CMD_TYPE	                            parseCommand();
        KEYWORD                                 parseKeyword();
        std::shared_ptr<Sort>	                parseSort();
        std::shared_ptr<DAGNode>		        parseExpr();
        std::vector<std::shared_ptr<DAGNode>>	parseParams();
        std::shared_ptr<DAGNode>		        parseLet();
        std::string                             parseGroup();
        std::string                             parseWeight();
        void                                    parseQuant(const std::string& type);
        
        // auxilary functions
        std::shared_ptr<DAGNode>	        bindLetVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>	        bindFunVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        //errors & warnings
        // mk errror node
        std::shared_ptr<DAGNode>	        mkErr(const ERROR_TYPE t);
        // error/warning information
        void 		err_all(const ERROR_TYPE e, const std::string s = "", const size_t ln = 0) const;
        void 		err_all(const std::shared_ptr<DAGNode> e, const std::string s = "", const size_t ln = 0) const;

        void 		err_unexp_eof() const;
        void 		err_sym_mis(const std::string mis, const size_t ln) const;
        void 		err_sym_mis(const std::string mis, const std::string nm, const size_t ln) const;
        void 		err_unkwn_sym(const std::string nm, const size_t ln) const;
        void 		err_param_mis(const std::string nm, const size_t ln) const;
        void 		err_param_nbool(const std::string nm, const size_t ln) const;
        void 		err_param_nnum(const std::string nm, const size_t ln) const;
        void 		err_param_nsame(const std::string nm, const size_t ln) const;
        void 		err_logic(const std::string nm, const size_t ln) const;
        void 		err_mul_decl(const std::string nm, const size_t ln) const;
        void 		err_mul_def(const std::string nm, const size_t ln) const;
        void 		err_zero_divisor(const size_t ln) const;
        void        err_arity_mis(const std::string nm, const size_t ln) const;
        void        err_keyword(const std::string nm, const size_t ln) const;
        void        err_type_mis(const std::string nm, const size_t ln) const;
        void        err_neg_param(const size_t ln) const;

        void		err_open_file(const std::string) const;

        void 		warn_cmd_nsup(const std::string nm, const size_t ln) const;


    };
}
#endif
