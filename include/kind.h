/* -*- Header -*-
 *
 * The Kind Enumeration
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

#ifndef _TYPES_H
#define _TYPES_H

#include <unordered_map>
#include <unordered_set>
#include <string>

namespace SMTParser{
    // common types
    enum class State {UNKNOWN=-1, UNSAT, SAT};

    enum class NODE_KIND {
        NT_UNKNOWN=0,NT_ERROR,NT_NULL, 
        // CORE OPERATORS
        NT_EQ,NT_DISTINCT,NT_EQ_BOOL,NT_EQ_OTHER,NT_DISTINCT_BOOL,NT_DISTINCT_OTHER, 

        // CONSTANT / VARIABLE
        NT_CONST,NT_VAR,NT_CONST_TRUE,NT_CONST_FALSE,NT_TEMP_VAR,
        // BOOLEAN
        NT_NOT,NT_AND,NT_OR,NT_IMPLIES,NT_XOR, 
        // UF
        NT_APPLY_UF,
        // ARITHMATIC COMMON OPERATORS
        NT_ADD,NT_MUL,NT_IAND,NT_POW2,NT_POW,NT_SUB,NT_NEG,NT_DIV_INT,NT_DIV_REAL,NT_MOD,NT_ABS,NT_SQRT,NT_SAFESQRT,NT_CEIL,NT_FLOOR,NT_ROUND,
        // TRANSCENDENTAL ARITHMATIC
        NT_EXP,NT_LOG,NT_LN,NT_LG,NT_LB,NT_SIN,NT_COS,NT_SEC,NT_CSC,NT_TAN,NT_COT,NT_ASIN,NT_ACOS,NT_ASEC,NT_ACSC,NT_ATAN,NT_ACOT,NT_SINH,NT_COSH,NT_TANH,NT_SECH,NT_CSCH,NT_COTH,NT_ASINH,NT_ACOSH,NT_ATANH,NT_ASECH,NT_ACSCH,NT_ACOTH,NT_ATAN2,
        // ARITHMATIC COMP
        NT_LE,NT_LT,NT_GE,NT_GT,
        // ARITHMATIC CONVERSION
        NT_TO_INT,NT_TO_REAL, 
        // ARITHMATIC PROPERTIES
        NT_IS_INT,NT_IS_DIVISIBLE,NT_IS_PRIME,NT_IS_EVEN,NT_IS_ODD,
        // ARITHMATIC CONSTANTS
        NT_CONST_PI,NT_CONST_E,NT_INFINITY,NT_NAN,NT_EPSILON,NT_POS_INFINITY,NT_NEG_INFINITY,NT_POS_EPSILON,NT_NEG_EPSILON,
        // ARITHMATIC FUNCTIONS
        //NT_SUM,NT_PROD, 
        NT_GCD,NT_LCM,NT_FACT,
        // BITVECTOR COMMON OPERATORS
        // Bit-wise operations
        NT_BV_NOT,NT_BV_AND,NT_BV_OR,NT_BV_XOR,NT_BV_NAND,NT_BV_NOR,NT_BV_XNOR,NT_BV_COMP,
        // Arithmetic operations
        NT_BV_NEG,NT_BV_ADD,NT_BV_SUB,NT_BV_MUL,NT_BV_UDIV,NT_BV_SDIV,NT_BV_UREM,NT_BV_SREM,NT_BV_UMOD,NT_BV_SMOD, 
        // Arithmetic operations with overflow
        NT_BV_NEGO,NT_BV_UADDO,NT_BV_SADDO,NT_BV_UMULO,NT_BV_SMULO,NT_BV_UDIVO,NT_BV_SDIVO,NT_BV_UREMO,NT_BV_SREMO,NT_BV_UMODO,NT_BV_SMODO,
        // Shift operations
        NT_BV_SHL,NT_BV_LSHR,NT_BV_ASHR, 
        // Function
        NT_BV_CONCAT,NT_BV_EXTRACT,NT_BV_REPEAT,NT_BV_ZERO_EXT,NT_BV_SIGN_EXT,NT_BV_ROTATE_LEFT,NT_BV_ROTATE_RIGHT, 
        // BITVECTOR COMP
        NT_BV_ULT,NT_BV_ULE,NT_BV_UGT,NT_BV_UGE,NT_BV_SLT,NT_BV_SLE,NT_BV_SGT,NT_BV_SGE, 
        // BITVECTOR CONVERSION
        NT_BV_TO_NAT,NT_NAT_TO_BV, NT_BV_TO_INT, NT_INT_TO_BV,
        // FINITE FIELD
        // FLOATING POINT COMMON OPERATORS
        NT_FP_ADD,NT_FP_SUB,NT_FP_MUL,NT_FP_DIV,NT_FP_ABS,NT_FP_NEG,NT_FP_REM,NT_FP_FMA,NT_FP_SQRT,NT_FP_ROUND_TO_INTEGRAL,NT_FP_MIN,NT_FP_MAX,
        // FLOATING POINT COMP
        NT_FP_LE,NT_FP_LT,NT_FP_GE,NT_FP_GT,NT_FP_EQ,NT_FP_NE,
        // FLOATING POINT CONVERSION
        NT_FP_TO_UBV,NT_FP_TO_SBV,NT_FP_TO_REAL,NT_FP_TO_FP,
        // FLOATING POINT PROPERTIES
        NT_FP_IS_NORMAL,NT_FP_IS_SUBNORMAL,NT_FP_IS_ZERO,NT_FP_IS_INF,NT_FP_IS_NAN,NT_FP_IS_NEG,NT_FP_IS_POS,
        // ARRAY
        NT_SELECT,NT_STORE, 
        // // DATATYPE
        //NT_CONSTRUCTOR,NT_TESTER,NT_SELECTOR,NT_ACCESSOR,NT_UPDATE,NT_DATATYPE_DEFAULT,
        // SET
        // RELATION
        // BAGS
        // STRINGS COMMON OPERATORS
        NT_STR_LEN,NT_STR_CONCAT,NT_STR_SUBSTR,NT_STR_INDEXOF,NT_STR_CHARAT,NT_STR_UPDATE,NT_STR_REPLACE,NT_STR_REPLACE_ALL,NT_STR_TO_LOWER,NT_STR_TO_UPPER,NT_STR_REV,NT_STR_SPLIT,NT_STR_SPLIT_AT,NT_STR_SPLIT_REST,NT_STR_NUM_SPLITS,
        // STRINGS COMP
        NT_STR_LT,NT_STR_LE,NT_STR_GT,NT_STR_GE,
        // STRINGS PROPERTIES
        NT_STR_IN_REG,NT_STR_CONTAINS,NT_STR_IS_DIGIT,NT_STR_PREFIXOF,NT_STR_SUFFIXOF,
        // STRINGS CONVERSION
        NT_STR_FROM_INT,NT_STR_TO_INT,NT_STR_TO_REG,NT_STR_TO_CODE,NT_STR_FROM_CODE, 
        // STRINGS RE CONSTANTS
        NT_REG_NONE,NT_REG_ALL,NT_REG_ALLCHAR, 
        // STRINGS RE COMMON OPERATORS
        NT_REG_CONCAT,NT_REG_UNION,NT_REG_INTER,NT_REG_DIFF,NT_REG_STAR,NT_REG_PLUS,NT_REG_OPT,NT_REG_RANGE,NT_REG_REPEAT,NT_REG_LOOP,NT_REG_COMPLEMENT,
        // STRINGS RE COMP
        // STRINGS RE PROPERTIES
        // STRINGS RE CONVERSION
        // STRINGS RE FUNCTIONS
        NT_REPLACE_REG, NT_REPLACE_REG_ALL,NT_INDEXOF_REG, 
        // SEQUENCE

        // INTERVAL
        NT_MAX, NT_MIN, 

        // LET (CHAIN)
        NT_LET, NT_LET_CHAIN,
        // LET BIND VAR (LIST)
        NT_LET_BIND_VAR, NT_LET_BIND_VAR_LIST,
        // ITE
        NT_ITE,
        // QUANTIFIERS
        NT_FORALL,NT_EXISTS, NT_QUANT_VAR,
        // FUNC
        NT_FUNC_DEC, // declare-fun, not for 0-arity functions (constant variables)
        NT_FUNC_DEF, // define-fun
        NT_FUNC_PARAM, // function parameter
        NT_FUNC_APPLY, // function application
        // NUM_KINDS
        NUM_KINDS
    };
    // NOTE: the last one is the number of kinds
    constexpr size_t NUM_KINDS = static_cast<size_t>(NODE_KIND::NUM_KINDS);
    const std::unordered_set<NODE_KIND> static_kinds = {
        NODE_KIND::NT_NULL,
        NODE_KIND::NT_UNKNOWN,
        NODE_KIND::NT_ERROR,
        NODE_KIND::NT_CONST_TRUE,
        NODE_KIND::NT_CONST_FALSE,
        NODE_KIND::NT_CONST_E,
        NODE_KIND::NT_CONST_PI,
        NODE_KIND::NT_NAN,
        NODE_KIND::NT_EPSILON,
        NODE_KIND::NT_POS_EPSILON,
        NODE_KIND::NT_NEG_EPSILON,
        NODE_KIND::NT_INFINITY,
        NODE_KIND::NT_POS_INFINITY,
        NODE_KIND::NT_NEG_INFINITY
    };
    // only used in preserving let mode
    const std::string PRESERVING_LET_BIND_VAR_SUFFIX = "_SMTParser_Preserving_Let_Bind_Var_Suffix_"; // +k
    const std::unordered_map<std::string, NODE_KIND> kind_key_map = {
        {"true", NODE_KIND::NT_CONST_TRUE},
        {"false", NODE_KIND::NT_CONST_FALSE},
        {"pi", NODE_KIND::NT_CONST_PI},
        {"e", NODE_KIND::NT_CONST_E},
        {"nan", NODE_KIND::NT_NAN},
        {"epsilon", NODE_KIND::NT_EPSILON},
        {"+epsilon", NODE_KIND::NT_POS_EPSILON},
        {"-epsilon", NODE_KIND::NT_NEG_EPSILON},
        {"+oo", NODE_KIND::NT_POS_INFINITY},
        {"-oo", NODE_KIND::NT_NEG_INFINITY},
        {"inf", NODE_KIND::NT_INFINITY},
    };
    const std::unordered_map<std::string, NODE_KIND> oper_key_map = {
        {"and", NODE_KIND::NT_AND},
        {"or", NODE_KIND::NT_OR},
        {"not", NODE_KIND::NT_NOT},
        {"=>", NODE_KIND::NT_IMPLIES},
        {"xor", NODE_KIND::NT_XOR},
        {"=", NODE_KIND::NT_EQ},
        {"==", NODE_KIND::NT_EQ},
        {"<->", NODE_KIND::NT_EQ},
        {"iff", NODE_KIND::NT_EQ},
        {"<=>", NODE_KIND::NT_EQ},
        {"distinct", NODE_KIND::NT_DISTINCT},
        {"!=", NODE_KIND::NT_DISTINCT},
        {"<>", NODE_KIND::NT_DISTINCT},
        {"ite", NODE_KIND::NT_ITE},
        {"+", NODE_KIND::NT_ADD},
        {"-", NODE_KIND::NT_SUB},
        {"*", NODE_KIND::NT_MUL},
        {"iand", NODE_KIND::NT_IAND},
        {"pow2", NODE_KIND::NT_POW2},
        {"pow", NODE_KIND::NT_POW},
        {"**", NODE_KIND::NT_POW},
        {"^", NODE_KIND::NT_POW},
        {"div", NODE_KIND::NT_DIV_INT},
        {"/", NODE_KIND::NT_DIV_REAL},
        {"mod", NODE_KIND::NT_MOD},
        {"abs", NODE_KIND::NT_ABS},
        {"sqrt", NODE_KIND::NT_SQRT},
        {"safeSqrt", NODE_KIND::NT_SAFESQRT},
        {"ceil", NODE_KIND::NT_CEIL},
        {"floor", NODE_KIND::NT_FLOOR},
        {"round", NODE_KIND::NT_ROUND},
        {"exp", NODE_KIND::NT_EXP},
        {"ln", NODE_KIND::NT_LN},
        {"loge", NODE_KIND::NT_LN},
        {"lg", NODE_KIND::NT_LG},
        {"log10", NODE_KIND::NT_LG},
        {"lb", NODE_KIND::NT_LB},
        {"log2", NODE_KIND::NT_LB},
        {"log", NODE_KIND::NT_LOG},
        {"sin", NODE_KIND::NT_SIN},
        {"cos", NODE_KIND::NT_COS},
        {"tan", NODE_KIND::NT_TAN},
        {"asin", NODE_KIND::NT_ASIN},
        {"arcsin", NODE_KIND::NT_ASIN},
        {"acos", NODE_KIND::NT_ACOS},
        {"arccos", NODE_KIND::NT_ACOS},
        {"atan", NODE_KIND::NT_ATAN},
        {"arctan", NODE_KIND::NT_ATAN},
        {"sinh", NODE_KIND::NT_SINH},
        {"cosh", NODE_KIND::NT_COSH},
        {"tanh", NODE_KIND::NT_TANH},
        {"asinh", NODE_KIND::NT_ASINH},
        {"arcsinh", NODE_KIND::NT_ASINH},
        {"acosh", NODE_KIND::NT_ACOSH},
        {"arccosh", NODE_KIND::NT_ACOSH},
        {"atanh", NODE_KIND::NT_ATANH},
        {"arctanh", NODE_KIND::NT_ATANH},
        {"asech", NODE_KIND::NT_ASECH},
        {"arcsec", NODE_KIND::NT_ASECH},
        {"acsch", NODE_KIND::NT_ACSCH},
        {"arccsch", NODE_KIND::NT_ACSCH},
        {"acoth", NODE_KIND::NT_ACOTH},
        {"arccoth", NODE_KIND::NT_ACOTH},
        {"atan2", NODE_KIND::NT_ATAN2},
        {"arctan2", NODE_KIND::NT_ATAN2},
        {"<=", NODE_KIND::NT_LE},
        {"<", NODE_KIND::NT_LT},
        {">=", NODE_KIND::NT_GE},
        {">", NODE_KIND::NT_GT},
        {"to_real", NODE_KIND::NT_TO_REAL},
        {"to_int", NODE_KIND::NT_TO_INT},
        {"is_int", NODE_KIND::NT_IS_INT},
        {"is_divisible", NODE_KIND::NT_IS_DIVISIBLE},
        {"is_prime", NODE_KIND::NT_IS_PRIME},
        {"is_even", NODE_KIND::NT_IS_EVEN},
        {"is_odd", NODE_KIND::NT_IS_ODD},
        {"gcd", NODE_KIND::NT_GCD},
        {"lcm", NODE_KIND::NT_LCM},
        {"factorial", NODE_KIND::NT_FACT},
        {"bvnot", NODE_KIND::NT_BV_NOT},
        {"bvneg", NODE_KIND::NT_BV_NEG},
        {"bvand", NODE_KIND::NT_BV_AND},
        {"bvor", NODE_KIND::NT_BV_OR},
        {"bvxor", NODE_KIND::NT_BV_XOR},
        {"bvnand", NODE_KIND::NT_BV_NAND},
        {"bvnor", NODE_KIND::NT_BV_NOR},
        {"bvxnor", NODE_KIND::NT_BV_XNOR},
        {"bvcomp", NODE_KIND::NT_BV_COMP},
        {"bvadd", NODE_KIND::NT_BV_ADD},
        {"bvsub", NODE_KIND::NT_BV_SUB},
        {"bvmul", NODE_KIND::NT_BV_MUL},
        {"bvudiv", NODE_KIND::NT_BV_UDIV},
        {"bvurem", NODE_KIND::NT_BV_UREM},
        {"bvsdiv", NODE_KIND::NT_BV_SDIV},
        {"bvsrem", NODE_KIND::NT_BV_SREM},
        {"bvsmod", NODE_KIND::NT_BV_SMOD},
        {"bvshl", NODE_KIND::NT_BV_SHL},
        {"bvlshr", NODE_KIND::NT_BV_LSHR},
        {"bvashr", NODE_KIND::NT_BV_ASHR},
        {"bvult", NODE_KIND::NT_BV_ULT},
        {"bvule", NODE_KIND::NT_BV_ULE},
        {"bvugt", NODE_KIND::NT_BV_UGT},
        {"bvuge", NODE_KIND::NT_BV_UGE},
        {"bvslt", NODE_KIND::NT_BV_SLT},
        {"bvsle", NODE_KIND::NT_BV_SLE},
        {"bvsgt", NODE_KIND::NT_BV_SGT},
        {"bvsge", NODE_KIND::NT_BV_SGE},
        {"concat", NODE_KIND::NT_BV_CONCAT},
        {"bv2nat", NODE_KIND::NT_BV_TO_NAT},
        {"nat2bv", NODE_KIND::NT_NAT_TO_BV},
        {"int2bv", NODE_KIND::NT_INT_TO_BV},
        {"bv2int", NODE_KIND::NT_BV_TO_INT},
        {"fp.abs", NODE_KIND::NT_FP_ABS},
        {"fp.neg", NODE_KIND::NT_FP_NEG},
        {"fp.add", NODE_KIND::NT_FP_ADD},
        {"fp.sub", NODE_KIND::NT_FP_SUB},
        {"fp.mul", NODE_KIND::NT_FP_MUL},
        {"fp.div", NODE_KIND::NT_FP_DIV},
        {"fp.fma", NODE_KIND::NT_FP_FMA},
        {"fp.sqrt", NODE_KIND::NT_FP_SQRT},
        {"fp.rem", NODE_KIND::NT_FP_REM},
        {"fp.roundToIntegral", NODE_KIND::NT_FP_ROUND_TO_INTEGRAL},
        {"fp.min", NODE_KIND::NT_FP_MIN},
        {"fp.max", NODE_KIND::NT_FP_MAX},
        {"fp.leq", NODE_KIND::NT_FP_LE},
        {"fp.lt", NODE_KIND::NT_FP_LT},
        {"fp.geq", NODE_KIND::NT_FP_GE},
        {"fp.gt", NODE_KIND::NT_FP_GT},
        {"fp.eq", NODE_KIND::NT_FP_EQ},
        {"fp.=", NODE_KIND::NT_FP_EQ},
        {"fp.==", NODE_KIND::NT_FP_EQ},
        {"fp.ne", NODE_KIND::NT_FP_NE},
        {"fp.!=", NODE_KIND::NT_FP_NE},
        {"fp.neq", NODE_KIND::NT_FP_NE},
        {"fp.to_ubv", NODE_KIND::NT_FP_TO_UBV},
        {"fp.to_sbv", NODE_KIND::NT_FP_TO_SBV},
        {"fp.to_real", NODE_KIND::NT_FP_TO_REAL},
        {"to_fp", NODE_KIND::NT_FP_TO_FP},
        {"fp.isNormal", NODE_KIND::NT_FP_IS_NORMAL},
        {"fp.isSubnormal", NODE_KIND::NT_FP_IS_SUBNORMAL},
        {"fp.isZero", NODE_KIND::NT_FP_IS_ZERO},
        {"fp.isInfinite", NODE_KIND::NT_FP_IS_INF},
        {"fp.isNaN", NODE_KIND::NT_FP_IS_NAN},
        {"fp.isNegative", NODE_KIND::NT_FP_IS_NEG},
        {"fp.isPositive", NODE_KIND::NT_FP_IS_POS},
        {"select", NODE_KIND::NT_SELECT},
        {"store", NODE_KIND::NT_STORE},
        {"str.len", NODE_KIND::NT_STR_LEN},
        {"str.++", NODE_KIND::NT_STR_CONCAT},
        {"str.substr", NODE_KIND::NT_STR_SUBSTR},
        {"str.prefixof", NODE_KIND::NT_STR_PREFIXOF},
        {"str.suffixof", NODE_KIND::NT_STR_SUFFIXOF},
        {"str.indexof", NODE_KIND::NT_STR_INDEXOF},
        {"str.at", NODE_KIND::NT_STR_CHARAT},
        {"str.update", NODE_KIND::NT_STR_UPDATE},
        {"str.replace", NODE_KIND::NT_STR_REPLACE},
        {"str.replace_all", NODE_KIND::NT_STR_REPLACE_ALL},
        {"str.replace_re", NODE_KIND::NT_REPLACE_REG},
        {"str.replace_re_all", NODE_KIND::NT_REPLACE_REG_ALL},
        {"str.to_lower", NODE_KIND::NT_STR_TO_LOWER},
        {"str.to_upper", NODE_KIND::NT_STR_TO_UPPER},
        {"str.rev", NODE_KIND::NT_STR_REV},
        {"str.split", NODE_KIND::NT_STR_SPLIT},
        {"str.split_at", NODE_KIND::NT_STR_SPLIT_AT},
        {"str.split_rest", NODE_KIND::NT_STR_SPLIT_REST},
        {"str.num_splits", NODE_KIND::NT_STR_NUM_SPLITS},
        {"str.<", NODE_KIND::NT_STR_LT},
        {"str.<=", NODE_KIND::NT_STR_LE},
        {"str.>", NODE_KIND::NT_STR_GT},
        {"str.>=", NODE_KIND::NT_STR_GE},
        {"str.in_re", NODE_KIND::NT_STR_IN_REG},
        {"str.contains", NODE_KIND::NT_STR_CONTAINS},
        {"str.is_digit", NODE_KIND::NT_STR_IS_DIGIT},
        {"str.from_int", NODE_KIND::NT_STR_FROM_INT},
        {"str.to_int", NODE_KIND::NT_STR_TO_INT},
        {"str.to_re", NODE_KIND::NT_STR_TO_REG},
        {"str.to_code", NODE_KIND::NT_STR_TO_CODE},
        {"str.from_code", NODE_KIND::NT_STR_FROM_CODE},
        {"re.++", NODE_KIND::NT_REG_CONCAT},
        {"re.union", NODE_KIND::NT_REG_UNION},
        {"re.inter", NODE_KIND::NT_REG_INTER},
        {"re.diff", NODE_KIND::NT_REG_DIFF},
        {"re.*", NODE_KIND::NT_REG_STAR},
        {"re.+", NODE_KIND::NT_REG_PLUS},
        {"re.?", NODE_KIND::NT_REG_OPT},
        {"re.opt", NODE_KIND::NT_REG_OPT},
        {"re.range", NODE_KIND::NT_REG_RANGE},
        {"re.repeat", NODE_KIND::NT_REG_REPEAT},
        {"re.comp", NODE_KIND::NT_REG_COMPLEMENT}
    };

    std::string kindToString(const NODE_KIND& nk);
    NODE_KIND getOppositeKind(const NODE_KIND& nk);
    NODE_KIND getKind(const std::string& s);
}



#endif
