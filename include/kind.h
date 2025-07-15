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

#include <string>
#include <unordered_set>

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

    std::string kindToString(const NODE_KIND& nk);
    NODE_KIND getOppositeKind(const NODE_KIND& nk);

    // only used in preserving let mode
    const std::string PRESERVING_LET_BIND_VAR_SUFFIX = "_SMTParser_Preserving_Let_Bind_Var_Suffix_"; // +k
}



#endif
