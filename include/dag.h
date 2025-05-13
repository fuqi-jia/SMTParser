/* -*- Header -*-
 *
 * The Directed Acyclic Graph (DAG) Class
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

#ifndef DAG_HEADER
#define DAG_HEADER

#include "kind.h"
#include "sort.h"
#include "util.h"

#include <iostream>
#include <fstream>
#include <cassert>

#include <string>
#include <vector>
#include <list>
#include <algorithm>
#include <ctime>
#include <cstdlib>
#include <memory>
#include <functional> // for std::hash

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

const double CONST_PI = 3.14159265358979323846;
const double CONST_E = 2.71828182845904523536;

namespace SMTLIBParser{
    class DAGNode {
    // <sort, kind, name> --- <sort, node_kind, name>
    private:
        std::shared_ptr<Sort>                   sort;
        NODE_KIND		                        kind;
        std::string		                        name;
        std::vector<std::shared_ptr<DAGNode>>   children;

        std::string                             children_hash;

    public:
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name, std::vector<std::shared_ptr<DAGNode>> children): sort(sort), kind(kind), name(name), children(children) {
            children_hash = "";
            for(auto& child : children){
                children_hash += child->hashString() + "__";
            }
            children_hash = sha256(children_hash);
        }
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name): sort(sort), kind(kind), name(name) {
            children_hash = "";
        }
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind): sort(sort), kind(kind), name("") {
            children_hash = "";
        }
        DAGNode(std::shared_ptr<Sort> sort): sort(sort), kind(NODE_KIND::NT_UNKNOWN), name("") {
            children_hash = "";
        }
        DAGNode(): sort(NULL_SORT), kind(NODE_KIND::NT_UNKNOWN), name(""), children_hash("") {}
        DAGNode(const DAGNode& other): sort(other.sort), kind(other.kind), name(other.name), children(other.children), children_hash(other.children_hash) {}

        // other initialization
        DAGNode(NODE_KIND kind, std::string name): sort(NULL_SORT), kind(kind), name(name) {
            children_hash = "";
        }
        DAGNode(NODE_KIND kind): sort(NULL_SORT), kind(kind), name("") {
            children_hash = "";
        }
        // only constant
        DAGNode(const std::string& n) {
            if (n == "true") {
                sort = BOOL_SORT;
                kind = NODE_KIND::NT_CONST_TRUE;
            } else if (n == "false") {
                sort = BOOL_SORT;
                kind = NODE_KIND::NT_CONST_FALSE;
            } else if (n == "pi") {
                sort = REAL_SORT;
                kind = NODE_KIND::NT_CONST_PI;
            } else if (n == "e") {
                sort = REAL_SORT;
                kind = NODE_KIND::NT_CONST_E;
            } else if (n == "inf") {
                sort = REAL_SORT;
                kind = NODE_KIND::NT_INFINITY;
            } else if (n == "NaN") {
                sort = REAL_SORT;
                kind = NODE_KIND::NT_NAN;
            } else if (n == "epsilon") {
                sort = REAL_SORT;
                kind = NODE_KIND::NT_EPSILON;
            } else if(n == "NULL") {
                sort = NULL_SORT;
                kind = NODE_KIND::NT_NULL;
            } else if(isIntUtil(n)){
                sort = INT_SORT;
                kind = NODE_KIND::NT_CONST;
            } else if(isRealUtil(n)){
                sort = REAL_SORT;
                kind = NODE_KIND::NT_CONST;
            } 
            // else if(isBVUtil(n)){
            //     sort = BV_SORT;
            //     kind = NODE_KIND::NT_CONST;
            // } 
            // else if(isFPUtil(n)){
            //     sort = FP_SORT;
            //     kind = NODE_KIND::NT_CONST;
            // } // not support
            else if(isStrUtil(n)){
                sort = STR_SORT;
                kind = NODE_KIND::NT_CONST;
            } else {
                sort = NULL_SORT;
                kind = NODE_KIND::NT_ERROR;
            }
            name = name;
            children_hash = "";
        }
        
        bool operator==(const DAGNode elem)
        {
            return (sort == elem.sort && kind == elem.kind && name == elem.name && children_hash == elem.children_hash);
        }
        
        bool isLeaf() 				const { return children.empty(); };
        bool isInternal() 			const { return !children.empty(); };

        // check null
        bool isNull() 				const { return kind == NODE_KIND::NT_NULL; };
        
        // check error
        bool isErr() 				const { return (kind == NODE_KIND::NT_ERROR); };

        // check const
        bool isCBool() 				const { return (kind == NODE_KIND::NT_CONST_TRUE || kind == NODE_KIND::NT_CONST_FALSE) && sort->isBool(); }; 
        bool isTrue() 				const { return kind == NODE_KIND::NT_CONST_TRUE && sort->isBool(); };
        bool isFalse() 			    const { return kind == NODE_KIND::NT_CONST_FALSE && sort->isBool(); };
        bool isConst() 				const { return  kind == NODE_KIND::NT_CONST || 
                                                    kind == NODE_KIND::NT_CONST_TRUE || kind == NODE_KIND::NT_CONST_FALSE ||
                                                    kind == NODE_KIND::NT_CONST_PI || kind == NODE_KIND::NT_CONST_E; };
        bool isCInt()       		const { return isConst() && (sort->isInt() || sort->isIntOrReal()); };
        bool isCRat()               const { return isConst() && (sort->isRat() || sort->isIntOrReal()); };
        bool isCReal()      		const { return isConst() && (sort->isReal() || sort->isRat() || sort->isIntOrReal()); };
        bool isCBV()        		const { return isConst() && sort->isBv(); };
        bool isCFP()        		const { return isConst() && sort->isFp(); };
        bool isCStr()       		const { return isConst() && sort->isStr(); };

        // check var
        bool isVBool() 				const { return kind == NODE_KIND::NT_VAR && sort->isBool(); };
        bool isVInt() 				const { return kind == NODE_KIND::NT_VAR && sort->isInt(); };
        bool isVReal() 				const { return kind == NODE_KIND::NT_VAR && sort->isReal(); };
        bool isVBV() 				const { return kind == NODE_KIND::NT_VAR && sort->isBv(); };
        bool isVFP() 				const { return kind == NODE_KIND::NT_VAR && sort->isFp(); };
        bool isVStr() 				const { return kind == NODE_KIND::NT_VAR && sort->isStr(); };
        bool isVar() 				const { return (isVBool() || isVInt() || isVReal() || isVBV() || isVFP() || isVStr()); };
        
        // check array
        bool isArray() 			    const { return kind == NODE_KIND::NT_VAR && sort->isArray(); };
        
        // check Boolean operations
        bool isAnd() 				const { return (kind == NODE_KIND::NT_AND); };
        bool isOr() 				const { return (kind == NODE_KIND::NT_OR); };
        bool isNot() 				const { return (kind == NODE_KIND::NT_NOT); };
        bool isImpl() 				const { return (kind == NODE_KIND::NT_IMPLIES); };
        bool isXor() 				const { return (kind == NODE_KIND::NT_XOR); };
        // bool isIteBool() 			const { return (kind == NODE_KIND::NT_ITE_BOOL); }; // 后面统一定义ite
        // bool isBoolOp() 			const { return (isAnd() || isOr() || isNot() || isImpl() || isXor() || isIteBool()); };
        // 其他操作也可以做得到bool op
        
        // check comparison
        bool isEqBool()             const { return (kind == NODE_KIND::NT_EQ_BOOL); };
        bool isEqOther()            const { return (kind == NODE_KIND::NT_EQ_OTHER); };
        bool isEq() 				const { return (kind == NODE_KIND::NT_EQ || isEqBool() || isEqOther()); };
        bool isDistinctBool()       const { return (kind == NODE_KIND::NT_DISTINCT_BOOL); };
        bool isDistinctOther()      const { return (kind == NODE_KIND::NT_DISTINCT_OTHER); };
        bool isDistinct() 			const { return (kind == NODE_KIND::NT_DISTINCT || isDistinctBool() || isDistinctOther()); };

        // check UF
        bool isApplyUF() 			const { return (kind == NODE_KIND::NT_APPLY_UF); };

        // check arithmetic operations
        bool isAdd() 				const { return (kind == NODE_KIND::NT_ADD); };
        bool isSub() 				const { return (kind == NODE_KIND::NT_SUB); };
        bool isMul() 				const { return (kind == NODE_KIND::NT_MUL); };
        bool isNeg() 				const { return (kind == NODE_KIND::NT_NEG); };
        bool isDivInt() 			const { return (kind == NODE_KIND::NT_DIV_INT); };
        bool isDivReal() 			const { return (kind == NODE_KIND::NT_DIV_REAL); };
        bool isMod() 				const { return (kind == NODE_KIND::NT_MOD); };
        bool isAbs() 				const { return (kind == NODE_KIND::NT_ABS); };
        bool isCeil() 				const { return (kind == NODE_KIND::NT_CEIL); };
        bool isFloor() 				const { return (kind == NODE_KIND::NT_FLOOR); };
        bool isRound() 				const { return (kind == NODE_KIND::NT_ROUND); };
        bool isArithOp() 			const { return (isAdd() || isSub() || isMul() || isNeg() || isDivInt() || isDivReal() || isMod() || isAbs() || isCeil() || isFloor() || isRound()); };
        
        // check transcendental operations
        bool isIAnd() 				const { return (kind == NODE_KIND::NT_IAND); };
        bool isPow2() 				const { return (kind == NODE_KIND::NT_POW2); };
        bool isPow() 				const { return (kind == NODE_KIND::NT_POW); };
        bool isSqrt() 				const { return (kind == NODE_KIND::NT_SQRT); };
        bool isSafeSqrt() 			const { return (kind == NODE_KIND::NT_SAFESQRT); };
        bool isRealNonlinearOp() 	const { return (isIAnd() || isPow2() || isPow() || isSqrt() || isSafeSqrt()); };
        bool isExp() 				const { return (kind == NODE_KIND::NT_EXP); };
        bool isLog() 				const { return (kind == NODE_KIND::NT_LOG); };
        bool isLn() 				const { return (kind == NODE_KIND::NT_LN); };
        bool isLb() 				const { return (kind == NODE_KIND::NT_LB); };
        bool isLg() 				const { return (kind == NODE_KIND::NT_LG); };
        bool isSin() 				const { return (kind == NODE_KIND::NT_SIN); };
        bool isCos() 				const { return (kind == NODE_KIND::NT_COS); };
        bool isSec() 				const { return (kind == NODE_KIND::NT_SEC); };
        bool isCsc() 				const { return (kind == NODE_KIND::NT_CSC); };
        bool isTan() 				const { return (kind == NODE_KIND::NT_TAN); };
        bool isCot() 				const { return (kind == NODE_KIND::NT_COT); };
        bool isAsin() 				const { return (kind == NODE_KIND::NT_ASIN); };
        bool isAcos() 				const { return (kind == NODE_KIND::NT_ACOS); };
        bool isAsec() 				const { return (kind == NODE_KIND::NT_ASEC); };
        bool isAcsc() 				const { return (kind == NODE_KIND::NT_ACSC); };
        bool isAtan() 				const { return (kind == NODE_KIND::NT_ATAN); };
        bool isAcot() 				const { return (kind == NODE_KIND::NT_ACOT); };
        bool isSinh() 				const { return (kind == NODE_KIND::NT_SINH); };
        bool isCosh() 				const { return (kind == NODE_KIND::NT_COSH); };
        bool isTanh() 				const { return (kind == NODE_KIND::NT_TANH); };
        bool isSech() 				const { return (kind == NODE_KIND::NT_SECH); };
        bool isCsch() 				const { return (kind == NODE_KIND::NT_CSCH); };
        bool isCoth() 				const { return (kind == NODE_KIND::NT_COTH); };
        bool isAsinh() 				const { return (kind == NODE_KIND::NT_ASINH); };
        bool isAcosh() 				const { return (kind == NODE_KIND::NT_ACOSH); };
        bool isAtanh() 				const { return (kind == NODE_KIND::NT_ATANH); };
        bool isAsech() 				const { return (kind == NODE_KIND::NT_ASECH); };
        bool isAcsch() 				const { return (kind == NODE_KIND::NT_ACSCH); };
        bool isAcoth() 				const { return (kind == NODE_KIND::NT_ACOTH); };
        bool isTranscendentalOp() 	const { return (isExp() || isLog() || isSin() || isCos() || isSec() || isCsc() || isTan() || isCot() || isAsin() || isAcos() || isAsec() || isAcsc() || isAtan() || isAcot() || isSinh() || isCosh() || isTanh() || isSech() || isCsch() || isCoth() || isAsinh() || isAcosh() || isAtanh() || isAsech() || isAcsch() || isAcoth()); };

        // check arithmetic comparison
        bool isLe() 				const { return (kind == NODE_KIND::NT_LE); };
        bool isLt() 				const { return (kind == NODE_KIND::NT_LT); };
        bool isGe() 				const { return (kind == NODE_KIND::NT_GE); };
        bool isGt() 				const { return (kind == NODE_KIND::NT_GT); };
        // bool isArithComp() 			const { return (isEq() || isDistinct() || isLe() || isLt() || isGe() || isGt()); };
        // eq不一定是算术比较

        // check arithmetic covertion
        bool isToReal() 			const { return (kind == NODE_KIND::NT_TO_REAL); };
        bool isToInt() 				const { return (kind == NODE_KIND::NT_TO_INT); };
        bool isArithConv() 			const { return (isToReal() || isToInt()); };

        // check arithmetic properties
        bool isInt() 				const { return (kind == NODE_KIND::NT_IS_INT); };
        bool isDivisible() 			const { return (kind == NODE_KIND::NT_IS_DIVISIBLE); };
        bool isPrime() 				const { return (kind == NODE_KIND::NT_IS_PRIME); };
        bool isEven() 				const { return (kind == NODE_KIND::NT_IS_EVEN); };
        bool isOdd() 				const { return (kind == NODE_KIND::NT_IS_ODD); };
        bool isArithProp() 			const { return (isInt() || isDivisible() || isPrime() || isEven() || isOdd()); };

        // check arithmetic constants
        bool isPi() 				const { return (kind == NODE_KIND::NT_CONST_PI); };
        bool isE() 					const { return (kind == NODE_KIND::NT_CONST_E); };
        bool isInfinity() 			const { return (kind == NODE_KIND::NT_INFINITY); };
        bool isNan() 				const { return (kind == NODE_KIND::NT_NAN); };
        bool isEpsilon() 			const { return (kind == NODE_KIND::NT_EPSILON); };
        // check arithmetic functions
        // bool isSum() 				const { return (kind == NODE_KIND::NT_SUM); };
        // bool isProd() 				const { return (kind == NODE_KIND::NT_PROD); };
        bool isGcd() 				const { return (kind == NODE_KIND::NT_GCD); };
        bool isLcm() 				const { return (kind == NODE_KIND::NT_LCM); };
        bool isFact() 				const { return (kind == NODE_KIND::NT_FACT); };
        // Bit-wise operations
        bool isBVNot() 				const { return (kind == NODE_KIND::NT_BV_NOT); };
        bool isBVAnd() 				const { return (kind == NODE_KIND::NT_BV_AND); };
        bool isBVOr() 				const { return (kind == NODE_KIND::NT_BV_OR); };
        bool isBVXor() 				const { return (kind == NODE_KIND::NT_BV_XOR); };
        bool isBVNand() 			const { return (kind == NODE_KIND::NT_BV_NAND); };
        bool isBVNor() 				const { return (kind == NODE_KIND::NT_BV_NOR); };
        bool isBVXnor() 			const { return (kind == NODE_KIND::NT_BV_XNOR); };
        bool isBVComp() 			const { return (kind == NODE_KIND::NT_BV_COMP); };
        // Arithmetic operations
        bool isBVNeg() 				const { return (kind == NODE_KIND::NT_BV_NEG); };
        bool isBVAdd() 				const { return (kind == NODE_KIND::NT_BV_ADD); };
        bool isBVSub() 				const { return (kind == NODE_KIND::NT_BV_SUB); };
        bool isBVMul() 				const { return (kind == NODE_KIND::NT_BV_MUL); };
        bool isBVUDiv() 			const { return (kind == NODE_KIND::NT_BV_UDIV); };
        bool isBVURem() 			const { return (kind == NODE_KIND::NT_BV_UREM); };
        bool isBVSdiv() 			const { return (kind == NODE_KIND::NT_BV_SDIV); };
        bool isBVSrem() 			const { return (kind == NODE_KIND::NT_BV_SREM); };
        bool isBVUmod() 			const { return (kind == NODE_KIND::NT_BV_UMOD); };
        bool isBVSmod() 			const { return (kind == NODE_KIND::NT_BV_SMOD); };
        // Arithmetic operations with overflow
        bool isBVNegO() 			const { return (kind == NODE_KIND::NT_BV_NEGO); };
        bool isBVUAddO() 			const { return (kind == NODE_KIND::NT_BV_UADDO); };
        bool isBVSAddO() 			const { return (kind == NODE_KIND::NT_BV_SADDO); };
        bool isBVUMulO() 			const { return (kind == NODE_KIND::NT_BV_UMULO); };
        bool isBVSMulO() 			const { return (kind == NODE_KIND::NT_BV_SMULO); };
        bool isBVUDivO() 			const { return (kind == NODE_KIND::NT_BV_UDIVO); };
        bool isBVSDivO() 			const { return (kind == NODE_KIND::NT_BV_SDIVO); };
        bool isBVURemO() 			const { return (kind == NODE_KIND::NT_BV_UREMO); };
        bool isBVSremO() 			const { return (kind == NODE_KIND::NT_BV_SREMO); };
        bool isBVUModO() 			const { return (kind == NODE_KIND::NT_BV_UMODO); };
        bool isBVSmodO() 			const { return (kind == NODE_KIND::NT_BV_SMODO); };
        // Shift operations
        bool isBVShl() 				const { return (kind == NODE_KIND::NT_BV_SHL); };
        bool isBVLSHR() 			const { return (kind == NODE_KIND::NT_BV_LSHR); };
        bool isBVAShr() 			const { return (kind == NODE_KIND::NT_BV_ASHR); };
        bool isBVConcat() 			const { return (kind == NODE_KIND::NT_BV_CONCAT); };
        bool isBVExtract() 			const { return (kind == NODE_KIND::NT_BV_EXTRACT); };
        bool isBVRepeat() 			const { return (kind == NODE_KIND::NT_BV_REPEAT); };
        bool isBVZeroExt() 			const { return (kind == NODE_KIND::NT_BV_ZERO_EXT); };
        bool isBVSignExt() 			const { return (kind == NODE_KIND::NT_BV_SIGN_EXT); };
        bool isBVRotLeft() 			const { return (kind == NODE_KIND::NT_BV_ROTATE_LEFT); };
        bool isBVRotRight() 		const { return (kind == NODE_KIND::NT_BV_ROTATE_RIGHT); };
        bool isBVOp() 	    		const { return (isBVNot() || isBVAnd() || isBVOr() || isBVXor() || isBVNand() || isBVNor() || isBVXnor() || isBVAdd() || isBVSub() || isBVMul() || isBVUDiv() || isBVURem() || isBVSdiv() || isBVSrem() || isBVSmod() || isBVShl() || isBVLSHR() || isBVAShr() || isBVConcat() || isBVExtract() || isBVRepeat() || isBVZeroExt() || isBVSignExt() || isBVRotLeft() || isBVRotRight()); };

        // check bitvector comparison
        bool isBVUlt() 	    		const { return (kind == NODE_KIND::NT_BV_ULT); };
        bool isBVUle() 	    		const { return (kind == NODE_KIND::NT_BV_ULE); };
        bool isBVUgt() 	    		const { return (kind == NODE_KIND::NT_BV_UGT); };
        bool isBVUge() 	    		const { return (kind == NODE_KIND::NT_BV_UGE); };
        bool isBVSLt() 	    		const { return (kind == NODE_KIND::NT_BV_SLT); };
        bool isBVSLe() 	    		const { return (kind == NODE_KIND::NT_BV_SLE); };
        bool isBVSGt() 	    		const { return (kind == NODE_KIND::NT_BV_SGT); };
        bool isBVSGe() 	    		const { return (kind == NODE_KIND::NT_BV_SGE); };
        bool isBVCompOp()     		const { return (isBVUlt() || isBVUle() || isBVUgt() || isBVUge() || isBVSLt() || isBVSLe() || isBVSGt() || isBVSGe()); };

        // check bitvector conversion
        bool isBVToNat() 			const { return (kind == NODE_KIND::NT_BV_TO_NAT); };
        bool isNatToBV() 			const { return (kind == NODE_KIND::NT_NAT_TO_BV); };
        bool isBVConv() 			const { return (isBVToNat() || isNatToBV()); };

        // check floating point common operators
        bool isFPAdd() 				const { return (kind == NODE_KIND::NT_FP_ADD); };
        bool isFPSub() 				const { return (kind == NODE_KIND::NT_FP_SUB); };
        bool isFPMul() 				const { return (kind == NODE_KIND::NT_FP_MUL); };
        bool isFPDiv() 				const { return (kind == NODE_KIND::NT_FP_DIV); };
        bool isFPAbs() 				const { return (kind == NODE_KIND::NT_FP_ABS); };
        bool isFPNeg() 				const { return (kind == NODE_KIND::NT_FP_NEG); };
        bool isFPRem() 				const { return (kind == NODE_KIND::NT_FP_REM); };
        bool isFPFMA() 				const { return (kind == NODE_KIND::NT_FP_FMA); };
        bool isFPSqrt() 			const { return (kind == NODE_KIND::NT_FP_SQRT); };
        bool isFPRoToInt()  		const { return (kind == NODE_KIND::NT_FP_ROUND_TO_INTEGRAL); };
        bool isFPMin() 				const { return (kind == NODE_KIND::NT_FP_MIN); };
        bool isFPMax() 				const { return (kind == NODE_KIND::NT_FP_MAX); };
        bool isFPOp() 				const { return (isFPAdd() || isFPSub() || isFPMul() || isFPDiv() || isFPAbs() || isFPNeg() || isFPRem() || isFPFMA() || isFPSqrt() || isFPRoToInt() || isFPMin() || isFPMax()); };

        // check floating point comparison
        bool isFPLe() 				const { return (kind == NODE_KIND::NT_FP_LE); };
        bool isFPLt() 				const { return (kind == NODE_KIND::NT_FP_LT); };
        bool isFPGe() 				const { return (kind == NODE_KIND::NT_FP_GE); };
        bool isFPGt() 				const { return (kind == NODE_KIND::NT_FP_GT); };
        bool isFPComp() 			const { return (isFPLe() || isFPLt() || isFPGe() || isFPGt()); };

        // check floating point conversion
        bool isFPToUBV() 			const { return (kind == NODE_KIND::NT_FP_TO_UBV); };
        bool isFPToSBV() 			const { return (kind == NODE_KIND::NT_FP_TO_SBV); };
        bool isFPToReal() 			const { return (kind == NODE_KIND::NT_FP_TO_REAL); };
        bool isToFP()     		    const { return (kind == NODE_KIND::NT_FP_TO_FP); };
        bool isFPConv() 			const { return (isFPToUBV() || isFPToSBV() || isFPToReal() || isToFP()); };

        // check floating point properties
        bool isFPIsNormal() 		const { return (kind == NODE_KIND::NT_FP_IS_NORMAL); };
        bool isFPIsSubnormal() 		const { return (kind == NODE_KIND::NT_FP_IS_SUBNORMAL); };
        bool isFPIsZero() 			const { return (kind == NODE_KIND::NT_FP_IS_ZERO); };
        bool isFPIsInf() 			const { return (kind == NODE_KIND::NT_FP_IS_INF); };
        bool isFPIsNan() 			const { return (kind == NODE_KIND::NT_FP_IS_NAN); };
        bool isFPIsNeg() 			const { return (kind == NODE_KIND::NT_FP_IS_NEG); };
        bool isFPIsPos() 			const { return (kind == NODE_KIND::NT_FP_IS_POS); };
        bool isFPProp() 			const { return isFPIsNormal() || isFPIsSubnormal() || isFPIsZero() || isFPIsInf() || isFPIsNan() || isFPIsNeg() || isFPIsPos(); }

        // check array
        bool isSelect() 			const { return (kind == NODE_KIND::NT_SELECT); };
        bool isStore() 				const { return (kind == NODE_KIND::NT_STORE); };
        bool isArrayOp() 			const { return (isSelect() || isStore()); };

        // check strings common operators
        bool isStrLen() 			const { return (kind == NODE_KIND::NT_STR_LEN); };
        bool isStrConcat() 			const { return (kind == NODE_KIND::NT_STR_CONCAT); };
        bool isStrSubstr() 			const { return (kind == NODE_KIND::NT_STR_SUBSTR); };
        bool isStrPrefixof() 		const { return (kind == NODE_KIND::NT_STR_PREFIXOF); };
        bool isStrSuffixof() 		const { return (kind == NODE_KIND::NT_STR_SUFFIXOF); };
        bool isStrIndexof() 		const { return (kind == NODE_KIND::NT_STR_INDEXOF); };
        bool isStrCharat() 			const { return (kind == NODE_KIND::NT_STR_CHARAT); };
        bool isStrUpdate() 			const { return (kind == NODE_KIND::NT_STR_UPDATE); };
        bool isStrReplace() 		const { return (kind == NODE_KIND::NT_STR_REPLACE); };
        bool isStrReplaceAll() 		const { return (kind == NODE_KIND::NT_STR_REPLACE_ALL); };
        bool isStrToLower() 		const { return (kind == NODE_KIND::NT_STR_TO_LOWER); };
        bool isStrToUpper() 		const { return (kind == NODE_KIND::NT_STR_TO_UPPER); };
        bool isStrRev() 			const { return (kind == NODE_KIND::NT_STR_REV); };
        bool isStrSplit() 			const { return (kind == NODE_KIND::NT_STR_SPLIT); };
        bool isStrOp() 				const { return (isStrLen() || isStrConcat() || isStrSubstr() || isStrPrefixof() || isStrSuffixof() || isStrIndexof() || isStrCharat() || isStrUpdate() || isStrReplace() || isStrReplaceAll() || isStrToLower() || isStrToUpper() || isStrRev() || isStrSplit()); };

        // check strings comparison
        bool isStrLt() 				const { return (kind == NODE_KIND::NT_STR_LT); };
        bool isStrLe() 				const { return (kind == NODE_KIND::NT_STR_LE); };
        bool isStrGt() 				const { return (kind == NODE_KIND::NT_STR_GT); };
        bool isStrGe() 				const { return (kind == NODE_KIND::NT_STR_GE); };

        // check strings properties
        bool isStrInReg() 			const { return (kind == NODE_KIND::NT_STR_IN_REG); };
        bool isStrContains() 		const { return (kind == NODE_KIND::NT_STR_CONTAINS); };
        bool isStrIsDigit() 		const { return (kind == NODE_KIND::NT_STR_IS_DIGIT); };

        // check strings conversion
        bool isStrFromInt() 		const { return (kind == NODE_KIND::NT_STR_FROM_INT); };
        bool isStrToInt() 			const { return (kind == NODE_KIND::NT_STR_TO_INT); };
        bool isStrToReg() 			const { return (kind == NODE_KIND::NT_STR_TO_REG); };
        bool isStrToCode() 			const { return (kind == NODE_KIND::NT_STR_TO_CODE); };
        bool isStrFromCode() 		const { return (kind == NODE_KIND::NT_STR_FROM_CODE); };
        bool isStrConv() 			const { return (isStrFromInt() || isStrToInt() || isStrToReg() || isStrToCode() || isStrFromCode()); };

        // check let
        bool isLet()				const { return kind == NODE_KIND::NT_LET; };

        // check ite
        bool isIte()				const { return kind == NODE_KIND::NT_ITE; };

        // check function
        bool isFuncDec()            const { return (kind == NODE_KIND::NT_FUNC_DEC); };
        bool isFuncDef()			const { return (kind == NODE_KIND::NT_FUNC_DEF); };
        bool isFuncParam()			const { return (kind == NODE_KIND::NT_FUNC_PARAM); };
        bool isFuncApply()          const { return (kind == NODE_KIND::NT_FUNC_APPLY); };

        std::string toString()      const { return name; };

        // other functions
        std::shared_ptr<Sort> getSort()
                                    const { return sort; };
        NODE_KIND getKind()         const { return kind; };
        std::string getName()       const { return name; };
        size_t getChildrenSize()    const { return children.size(); };
        std::vector<std::shared_ptr<DAGNode>> getChildren() 
                                    const { return children; };
        std::shared_ptr<DAGNode> getChild(int i) 
                                    const { return children[i]; };
        // NOTE: function body is the first child
        std::shared_ptr<DAGNode> getFuncBody() 
                                    const { return children[0]; };
        std::vector<std::shared_ptr<DAGNode>> getFuncParams() const{
            std::vector<std::shared_ptr<DAGNode>> res;
            for(size_t i = 1;i<getChildrenSize();i++){
                res.emplace_back(getChild(i));
            }
            return res;
        }
        void updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params);
        void updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params);
        

        std::shared_ptr<DAGNode> getQuantBody() const { return children[0]; };
        std::vector<std::shared_ptr<DAGNode>> getQuantVars() const{
            std::vector<std::shared_ptr<DAGNode>> res;
            for(size_t i = 1;i<getChildrenSize();i++){
                res.emplace_back(getChild(i));
            }
            return res;
        }

        // convert to integer
        Integer toInt() const {
            assert(isCInt());
            return Integer(name);
        }
        // convert to real
        Real toReal() const {
            assert(isCReal());
            if(isCRat()){
                return Real(toRat());
            }
            if(name == "pi"){
                return Real(CONST_PI);
            }
            if(name == "e"){
                return Real(CONST_E);
            }

            return Real(name);
        }
        // convert to rational
        Rational toRat() const {
            assert(isCRat());
            return Rational(name);
        }

        // check if it is zero
        bool isZero() const {
            if(isCInt()){
                return toInt() == 0;
            }
            else if(isCReal()){
                return toReal() == 0.0;
            }
            else if(isCRat()){
                return toRat() == 0;
            }
            else if(isCBV()){
                return Integer(bvToNat(name)) == 0;
            }
            return false;
        }

        // check if it is one
        bool isOne() const {
            if(isCInt()){
                return toInt() == 1;
            }
            else if(isCReal()){
                return toReal() == 1.0;
            }
            else if(isCRat()){
                return toRat() == 1;
            }
            return false;
        }


        // is really equal to another node
        bool isEquivalentTo(const DAGNode& other) const {
            if(hashString() != other.hashString()) {
                return false;
            }
            
            if (sort != other.sort || kind != other.kind || name != other.name || children.size() != other.children.size()) {
                return false;
            }
            for (size_t i = 0; i < children.size(); i++) {
                if (!children[i]->isEquivalentTo(*other.children[i])) {
                    return false;
                }
            }
            return true;
        }

        std::string hashString() const {
            return sha256(sort->toString() + "__" + kindToString(kind) + "__" + name + "__" + std::to_string(children.size()) + "__" + children_hash);
        }

        std::size_t hashCode() const{
            return std::hash<std::string>{}(hashString());
        }
    };

    inline const std::shared_ptr<DAGNode> NULL_NODE = std::make_shared<DAGNode>(NODE_KIND::NT_NULL);


    struct NodeHash {
        size_t operator()(const std::shared_ptr<DAGNode>& node) const {
            return std::hash<std::string>{}(node->hashString());
        }
    };

    struct NodeEqual {
        bool operator()(const std::shared_ptr<DAGNode>& node1, const std::shared_ptr<DAGNode>& node2) const {
            return node1->isEquivalentTo(*node2);
        }
    };

    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& node);
    std::string dumpFuncDef(const std::shared_ptr<DAGNode>& node);
    std::string dumpFuncDec(const std::shared_ptr<DAGNode>& node);
    std::string dumpSMTLIB2(const std::vector<std::shared_ptr<DAGNode>>& assertions);
    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& node, std::ofstream& ofs);
    void dumpSMTLIB2(const std::shared_ptr<DAGNode>& node, boost::unordered_set<std::shared_ptr<DAGNode>>& visited, std::ofstream& ofs);
    void dumpSMTLIB2(const std::vector<std::shared_ptr<DAGNode>>& assertions, std::ofstream& ofs);
    void dumpFuncDef(const std::shared_ptr<DAGNode>& node, std::ofstream& ofs);
    void dumpFuncDec(const std::shared_ptr<DAGNode>& node, std::ofstream& ofs);
}
#endif