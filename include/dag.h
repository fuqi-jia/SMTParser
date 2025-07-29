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
#include "value.h"
#include "timing.h"

#include <iostream>
#include <fstream>

#include <string>
#include <vector>
#include <list>
#include <algorithm>
#include <ctime>
#include <cstdlib>
#include <memory>
#include <functional> // for std::hash

#include <unordered_map>
#include <unordered_set>
#include <array>

namespace SMTParser{
    // Forward declaration of DAGNode class
    class DAGNode;
    
    // define hash function and equal function for std::pair<const DAGNode*, const DAGNode*>
    struct PairNodePtrHash {
        size_t operator()(const std::pair<const DAGNode*, const DAGNode*>& p) const {
            return std::hash<const void*>()(p.first) ^ std::hash<const void*>()(p.second);
        }
    };

    struct PairNodePtrEqual {
        bool operator()(const std::pair<const DAGNode*, const DAGNode*>& p1, const std::pair<const DAGNode*, const DAGNode*>& p2) const {
            return p1.first == p2.first && p1.second == p2.second;
        }
    };

    class DAGNode {
    // <sort, kind, name> --- <sort, node_kind, name>
    private:
        std::shared_ptr<Sort>                   sort;
        NODE_KIND		                        kind;
        std::string		                        name;
        std::shared_ptr<Value>                  value;
        std::vector<std::shared_ptr<DAGNode>>   children;

        std::string                             children_hash;
        mutable size_t                          cached_hash_code;
        mutable bool                            hash_computed;
        mutable size_t                          _use_count;

    public:
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name, std::vector<std::shared_ptr<DAGNode>> children): sort(sort), kind(kind), name(name), value(nullptr), children(children){
            // value is not used for hash
            if(children.empty()) {
                children_hash = "";
            } else {
                size_t combined_hash = 0;
                for(size_t i = 0; i < children.size(); i++) {
                    size_t child_hash = children[i]->hashCode();
                    combined_hash ^= child_hash + 0x9e3779b9 + (combined_hash << 6) + (combined_hash >> 2);
                }
                children_hash = std::to_string(combined_hash);
            }
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;

            if(kind == NODE_KIND::NT_CONST){
                if(TypeChecker::isInt(name)){
                    value = newValue(Number(name, true));
                } else if(TypeChecker::isReal(name)){
                    value = newValue(Number(name, false));
                } 
                // TODO for value
            }
        }
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name): sort(sort), kind(kind), name(name), value(nullptr) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;

            if(kind == NODE_KIND::NT_CONST){
                if(TypeChecker::isInt(name)){
                    value = newValue(Number(name, true));
                } else if(TypeChecker::isReal(name)){
                    value = newValue(Number(name, false));
                }
                // TODO for value
            }
        }
        DAGNode(std::shared_ptr<Sort> sort, NODE_KIND kind): sort(sort), kind(kind), name(""), value(nullptr) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            
            if(kind == NODE_KIND::NT_CONST){
                value = newValue(Number());
            }
        }
        DAGNode(std::shared_ptr<Sort> sort): sort(sort), kind(NODE_KIND::NT_UNKNOWN), name(""), value(nullptr) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;

            if(kind == NODE_KIND::NT_CONST){
                value = newValue(Number());
            }
        }
        DAGNode(): sort(NULL_SORT), kind(NODE_KIND::NT_UNKNOWN), name(""), value(nullptr), children_hash(""), cached_hash_code(0), hash_computed(false), _use_count(1) {
            children_hash = "";
        }
        DAGNode(const DAGNode& other): sort(other.sort), kind(other.kind), name(other.name), value(other.value), children(other.children), children_hash(other.children_hash), cached_hash_code(0), hash_computed(false), _use_count(1) {}

        // other initialization
        DAGNode(NODE_KIND kind, std::string name): sort(NULL_SORT), kind(kind), name(name), value(nullptr) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;

            if(kind == NODE_KIND::NT_CONST){
                if(TypeChecker::isInt(name)){
                    value = newValue(Number(name, true));
                } else if(TypeChecker::isReal(name)){
                    value = newValue(Number(name, false));
                } 
            }
        }
        DAGNode(NODE_KIND kind): sort(NULL_SORT), kind(kind), name(""), value(nullptr) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;

            if(kind == NODE_KIND::NT_CONST){
                value = newValue(Number());
            }
        }
        DAGNode(std::shared_ptr<Sort> sort, const Integer& v): sort(sort), kind(NODE_KIND::NT_CONST), name(""), value(newValue(v)) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            name = v.toString();
        }
        DAGNode(std::shared_ptr<Sort> sort, const Real& v): sort(sort), kind(NODE_KIND::NT_CONST), name(""), value(newValue(v)) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            name = v.toString();
        }
        DAGNode(std::shared_ptr<Sort> sort, const double& v): sort(sort), kind(NODE_KIND::NT_CONST), name(""), value(newValue(v)) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            name = std::to_string(v);
        }
        DAGNode(std::shared_ptr<Sort> sort, const int& v): sort(sort), kind(NODE_KIND::NT_CONST), name(""), value(newValue(v)) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            name = std::to_string(v);
        }
        DAGNode(std::shared_ptr<Sort> sort, const bool& v): sort(sort), kind(NODE_KIND::NT_CONST), name(""), value(newValue(v)) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
            name = v ? "true" : "false";
        }
        
        // only constant
        DAGNode(const std::string& n) {
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            _use_count = 0;
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
            } else if(TypeChecker::isInt(n)){
                sort = INT_SORT;
                kind = NODE_KIND::NT_CONST;
                value = newValue(Number(n, true));
            } else if(TypeChecker::isReal(n)){
                sort = REAL_SORT;
                kind = NODE_KIND::NT_CONST;
                value = newValue(Number(n, false));
            } 
            else if(TypeChecker::isString(n)){
                sort = STR_SORT;
                kind = NODE_KIND::NT_CONST;
            } else {
                sort = NULL_SORT;
                kind = NODE_KIND::NT_ERROR;
            }
            name = n;
        }
        
        void clear(){
            kind = NODE_KIND::NT_ERROR;
            children.clear();
            children_hash = "";
            cached_hash_code = 0;
            hash_computed = false;
            name = "";
            _use_count = 0;
        }

        bool operator==(const DAGNode elem)
        {
            return (sort == elem.sort && kind == elem.kind && name == elem.name && children_hash == elem.children_hash);
        }
        bool operator!=(const DAGNode elem)
        {
            return (sort != elem.sort || kind != elem.kind || name != elem.name || children_hash != elem.children_hash);
        }
        
        bool isLeaf() 				const { return children.empty(); };
        bool isInternal() 			const { return !children.empty(); };

        // check null
        bool isNull() 				const { return kind == NODE_KIND::NT_NULL; };
        
        // check error
        bool isErr() 				const { return (kind == NODE_KIND::NT_ERROR); };

        // check unknown
        bool isUnknown() 			const { return kind == NODE_KIND::NT_UNKNOWN; };

        // check const
        bool isCBool() 				const { return (kind == NODE_KIND::NT_CONST_TRUE || kind == NODE_KIND::NT_CONST_FALSE) && sort->isBool(); }; 
        bool isTrue() 				const { return kind == NODE_KIND::NT_CONST_TRUE && sort->isBool(); };
        bool isFalse() 			    const { return kind == NODE_KIND::NT_CONST_FALSE && sort->isBool(); };
        bool isConst() 				const { return  kind == NODE_KIND::NT_CONST || 
                                                    kind == NODE_KIND::NT_CONST_TRUE || kind == NODE_KIND::NT_CONST_FALSE ||
                                                    kind == NODE_KIND::NT_CONST_PI || kind == NODE_KIND::NT_CONST_E; };
        bool isNumeral() 			const { return isCInt() || isCReal(); };
        bool isCInt()       		const { return isConst() && (sort->isInt() || sort->isIntOrReal()); };
        bool isCReal()      		const { return isConst() && (sort->isReal() || sort->isIntOrReal()); };
        bool isCBV()        		const { return isConst() && sort->isBv(); };
        bool isCFP()        		const { return isConst() && sort->isFp(); };
        bool isCStr()       		const { return isConst() && sort->isStr(); };

        // check var
        bool isVBool() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isBool(); };
        bool isLiteral() 			const { return (isVBool() || (isNot() && getChild(0)->isVBool()) || isCBool()); };
        bool isVInt() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isInt(); };
        bool isVReal() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isReal(); };
        bool isVBV() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isBv(); };
        bool isVFP() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isFp(); };
        bool isVStr() 				const { return (kind == NODE_KIND::NT_VAR || kind == NODE_KIND::NT_TEMP_VAR || kind == NODE_KIND::NT_QUANT_VAR || kind == NODE_KIND::NT_LET_BIND_VAR) && sort->isStr(); };
        bool isTempVar() 			const { return kind == NODE_KIND::NT_TEMP_VAR; };
        bool isQuantVar() 			const { return kind == NODE_KIND::NT_QUANT_VAR; };
        bool isLetBindVar() 		const { return kind == NODE_KIND::NT_LET_BIND_VAR; };
        bool isVar() 				const { return (isVBool() || isVInt() || isVReal() || isVBV() || isVFP() || isVStr() || isTempVar() || isQuantVar() || isLetBindVar()); };
        
        // interval
        bool isMax() 				const { return kind == NODE_KIND::NT_MAX; };
        bool isMin() 				const { return kind == NODE_KIND::NT_MIN; };

        // check array
        bool isArray() 			    const { return kind == NODE_KIND::NT_VAR && sort->isArray(); };
        
        // check Boolean operations
        bool isAnd() 				const { return (kind == NODE_KIND::NT_AND); };
        bool isOr() 				const { return (kind == NODE_KIND::NT_OR); };
        bool isNot() 				const { return (kind == NODE_KIND::NT_NOT); };
        bool isImplies() 				const { return (kind == NODE_KIND::NT_IMPLIES); };
        bool isXor() 				const { return (kind == NODE_KIND::NT_XOR); };
        
        // check comparison
        bool isEqBool()             const { return (kind == NODE_KIND::NT_EQ_BOOL); };
        bool isEqOther()            const { return (kind == NODE_KIND::NT_EQ_OTHER); };
        bool isEq() 				const { return (kind == NODE_KIND::NT_EQ || isEqBool() || isEqOther()); };
        bool isDistinctBool()       const { return (kind == NODE_KIND::NT_DISTINCT_BOOL); };
        bool isDistinctOther()      const { return (kind == NODE_KIND::NT_DISTINCT_OTHER); };
        bool isDistinct() 			const { return (kind == NODE_KIND::NT_DISTINCT || isDistinctBool() || isDistinctOther()); };
        bool isNeq() 				const { return isDistinct(); };

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
        bool isAtan2() 				const { return (kind == NODE_KIND::NT_ATAN2); };
        bool isTranscendentalOp() 	const { return (isExp() || isLog() || isLn() || isLb() || isLg() || isSin() || isCos() || isSec() || isCsc() || isTan() || isCot() || isAsin() || isAcos() || isAsec() || isAcsc() || isAtan() || isAcot() || isSinh() || isCosh() || isTanh() || isSech() || isCsch() || isCoth() || isAsinh() || isAcosh() || isAtanh() || isAsech() || isAcsch() || isAcoth() || isAtan2()); };

        // check arithmetic comparison
        bool isLe() 				const { return (kind == NODE_KIND::NT_LE); };
        bool isLt() 				const { return (kind == NODE_KIND::NT_LT); };
        bool isGe() 				const { return (kind == NODE_KIND::NT_GE); };
        bool isGt() 				const { return (kind == NODE_KIND::NT_GT); };
        bool isArithTerm() 			const { return (isArithOp() || isArithConv() || isRealNonlinearOp() || isTranscendentalOp() || 
                                                    (isVar() && (isVInt() || isVReal())) ||
                                                    (isConst() && (isCInt() || isCReal())) ||
                                                    ((isIte() || isMax() || isMin() || isApplyUF()) && (sort->isInt() || sort->isReal()))); };
        bool isArithComp() 			const { return ((isEq() && getChild(0)->isArithTerm())|| 
                                                    (isDistinct() && getChild(0)->isArithTerm()) || 
                                                    isLe() || isLt() || isGe() || isGt()); };

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
        bool isInfinity() 			const { return (kind == NODE_KIND::NT_INFINITY || kind == NODE_KIND::NT_POS_INFINITY || kind == NODE_KIND::NT_NEG_INFINITY); };
        bool isPosInfinity() 		const { return (kind == NODE_KIND::NT_POS_INFINITY); };
        bool isNegInfinity() 		const { return (kind == NODE_KIND::NT_NEG_INFINITY); };
        bool isNan() 				const { return (kind == NODE_KIND::NT_NAN); };
        bool isEpsilon() 			const { return (kind == NODE_KIND::NT_EPSILON || kind == NODE_KIND::NT_POS_EPSILON || kind == NODE_KIND::NT_NEG_EPSILON ); };
        bool isPosEpsilon() 		const { return (kind == NODE_KIND::NT_POS_EPSILON); };
        bool isNegEpsilon() 		const { return (kind == NODE_KIND::NT_NEG_EPSILON); };

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
        bool isBVSDiv() 			const { return (kind == NODE_KIND::NT_BV_SDIV); };
        bool isBVSRem() 			const { return (kind == NODE_KIND::NT_BV_SREM); };
        bool isBVUMod() 			const { return (kind == NODE_KIND::NT_BV_UMOD); };
        bool isBVSMod() 			const { return (kind == NODE_KIND::NT_BV_SMOD); };
        // Arithmetic operations with overflow
        bool isBVNegO() 			const { return (kind == NODE_KIND::NT_BV_NEGO); };
        bool isBVUAddO() 			const { return (kind == NODE_KIND::NT_BV_UADDO); };
        bool isBVSAddO() 			const { return (kind == NODE_KIND::NT_BV_SADDO); };
        bool isBVUMulO() 			const { return (kind == NODE_KIND::NT_BV_UMULO); };
        bool isBVSMulO() 			const { return (kind == NODE_KIND::NT_BV_SMULO); };
        bool isBVUDivO() 			const { return (kind == NODE_KIND::NT_BV_UDIVO); };
        bool isBVSDivO() 			const { return (kind == NODE_KIND::NT_BV_SDIVO); };
        bool isBVURemO() 			const { return (kind == NODE_KIND::NT_BV_UREMO); };
        bool isBVSRemO() 			const { return (kind == NODE_KIND::NT_BV_SREMO); };
        bool isBVUModO() 			const { return (kind == NODE_KIND::NT_BV_UMODO); };
        bool isBVSModO() 			const { return (kind == NODE_KIND::NT_BV_SMODO); };
        // Shift operations
        bool isBVShl() 				const { return (kind == NODE_KIND::NT_BV_SHL); };
        bool isBVLSHR() 			const { return (kind == NODE_KIND::NT_BV_LSHR); };
        bool isBVASHR() 			const { return (kind == NODE_KIND::NT_BV_ASHR); };
        bool isBVConcat() 			const { return (kind == NODE_KIND::NT_BV_CONCAT); };
        bool isBVExtract() 			const { return (kind == NODE_KIND::NT_BV_EXTRACT); };
        bool isBVRepeat() 			const { return (kind == NODE_KIND::NT_BV_REPEAT); };
        bool isBVZeroExt() 			const { return (kind == NODE_KIND::NT_BV_ZERO_EXT); };
        bool isBVSignExt() 			const { return (kind == NODE_KIND::NT_BV_SIGN_EXT); };
        bool isBVRotLeft() 			const { return (kind == NODE_KIND::NT_BV_ROTATE_LEFT); };
        bool isBVRotRight() 		const { return (kind == NODE_KIND::NT_BV_ROTATE_RIGHT); };
        bool isBVOp() 	    		const { return (isBVNot() || isBVAnd() || isBVOr() || isBVXor() || isBVNand() || isBVNor() || isBVXnor() || isBVAdd() || isBVSub() || isBVMul() || isBVUDiv() || isBVURem() || isBVSDiv() || isBVSRem() || isBVSMod() || isBVShl() || isBVLSHR() || isBVASHR() || isBVConcat() || isBVExtract() || isBVRepeat() || isBVZeroExt() || isBVSignExt() || isBVRotLeft() || isBVRotRight()); };

        // check bitvector comparison
        bool isBVUlt() 	    		const { return (kind == NODE_KIND::NT_BV_ULT); };
        bool isBVUle() 	    		const { return (kind == NODE_KIND::NT_BV_ULE); };
        bool isBVUgt() 	    		const { return (kind == NODE_KIND::NT_BV_UGT); };
        bool isBVUge() 	    		const { return (kind == NODE_KIND::NT_BV_UGE); };
        bool isBVSlt() 	    		const { return (kind == NODE_KIND::NT_BV_SLT); };
        bool isBVSle() 	    		const { return (kind == NODE_KIND::NT_BV_SLE); };
        bool isBVSgt() 	    		const { return (kind == NODE_KIND::NT_BV_SGT); };
        bool isBVSge() 	    		const { return (kind == NODE_KIND::NT_BV_SGE); };
        bool isBVTerm()    		    const { return (isBVOp() ||
                                                    (isVar() && isVBV()) ||
                                                    (isConst() && isCBV()) ||
                                                    (isIte() && getChild(1)->isBVTerm() && getChild(2)->isBVTerm()) ||
                                                    (isMax() && getChild(0)->isBVTerm() && getChild(1)->isBVTerm()) ||
                                                    (isMin() && getChild(0)->isBVTerm() && getChild(1)->isBVTerm()) ||
                                                    (isApplyUF() && sort->isBv())); };
        bool isBVCompOp()     		const { return ((isEq() && getChild(0)->isBVTerm()) ||
                                                    (isDistinct() && getChild(0)->isBVTerm()) ||
                                                    isBVUlt() || isBVUle() || isBVUgt() || isBVUge() || isBVSlt() || isBVSle() || isBVSgt() || isBVSge()); };
        bool isBvAtom()             const { return isBVCompOp(); }; 

        // check bitvector conversion
        bool isBVToNat() 			const { return (kind == NODE_KIND::NT_BV_TO_NAT); };
        bool isNatToBV() 			const { return (kind == NODE_KIND::NT_NAT_TO_BV); };
        bool isBVToInt() 			const { return (kind == NODE_KIND::NT_BV_TO_INT); };
        bool isIntToBV() 			const { return (kind == NODE_KIND::NT_INT_TO_BV); };
        bool isBVConv() 			const { return (isBVToNat() || isNatToBV() || isBVToInt() || isIntToBV()); };

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
        bool isFPRoundToIntegral()  const { return (kind == NODE_KIND::NT_FP_ROUND_TO_INTEGRAL); };
        bool isFPRoToInt()  		const { return (kind == NODE_KIND::NT_FP_ROUND_TO_INTEGRAL); };
        bool isFPMin() 				const { return (kind == NODE_KIND::NT_FP_MIN); };
        bool isFPMax() 				const { return (kind == NODE_KIND::NT_FP_MAX); };
        bool isFPOp() 				const { return (isFPAdd() || isFPSub() || isFPMul() || isFPDiv() || isFPAbs() || isFPNeg() || isFPRem() || isFPFMA() || isFPSqrt() || isFPRoToInt() || isFPMin() || isFPMax() || (isApplyUF() && sort->isFp())); };

        // check floating point comparison
        bool isFPLe() 				const { return (kind == NODE_KIND::NT_FP_LE); };
        bool isFPLt() 				const { return (kind == NODE_KIND::NT_FP_LT); };
        bool isFPGe() 				const { return (kind == NODE_KIND::NT_FP_GE); };
        bool isFPGt() 				const { return (kind == NODE_KIND::NT_FP_GT); };
        bool isFPEq() 				const { return (kind == NODE_KIND::NT_FP_EQ); };
        bool isFPNe() 				const { return (kind == NODE_KIND::NT_FP_NE); };
        bool isFPComp() 			const { return (isFPLe() || isFPLt() || isFPGe() || isFPGt() || isFPEq() || isFPNe()); };

        // check floating point conversion
        bool isFPToUBV() 			const { return (kind == NODE_KIND::NT_FP_TO_UBV); };
        bool isFPToSBV() 			const { return (kind == NODE_KIND::NT_FP_TO_SBV); };
        bool isFPToReal() 			const { return (kind == NODE_KIND::NT_FP_TO_REAL); };
        bool isToFP()     		    const { return (kind == NODE_KIND::NT_FP_TO_FP); };
        bool isToFPUnsigned()       const { return (kind == NODE_KIND::NT_FP_TO_FP_UNSIGNED); };

        bool isFPConv() 			const { return (isFPToUBV() || isFPToSBV() || isFPToReal() || isToFP() || isToFPUnsigned()); };

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
        bool isArrayOp() 			const { return (isSelect() || isStore() || (isApplyUF() && sort->isArray())); };

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
        bool isStrSplitAt() 		const { return (kind == NODE_KIND::NT_STR_SPLIT_AT); };
        bool isStrSplitRest() 		const { return (kind == NODE_KIND::NT_STR_SPLIT_REST); };
        bool isStrNumSplits() 		const { return (kind == NODE_KIND::NT_STR_NUM_SPLITS); };
        bool isStrSplitAtRe() 		const { return (kind == NODE_KIND::NT_STR_SPLIT_AT_RE); };
        bool isStrSplitRestRe() 		const { return (kind == NODE_KIND::NT_STR_SPLIT_REST_RE); };
        bool isStrNumSplitsRe() 		const { return (kind == NODE_KIND::NT_STR_NUM_SPLITS_RE); };
        bool isStrOp() 				const { return (isStrLen() || isStrConcat() || isStrSubstr() || isStrPrefixof() || isStrSuffixof() || isStrIndexof() || isStrCharat() || isStrUpdate() || isStrReplace() || isStrReplaceAll() || isStrToLower() || isStrToUpper() || isStrRev() || isStrSplit() || isStrSplitAt() || isStrSplitRest() || isStrNumSplits() || isStrSplitAtRe() || isStrSplitRestRe() || isStrNumSplitsRe() || (isApplyUF() && sort->isStr())); };

        // check strings comparison
        bool isStrLt() 				const { return (kind == NODE_KIND::NT_STR_LT); };
        bool isStrLe() 				const { return (kind == NODE_KIND::NT_STR_LE); };
        bool isStrGt() 				const { return (kind == NODE_KIND::NT_STR_GT); };
        bool isStrGe() 				const { return (kind == NODE_KIND::NT_STR_GE); };
        bool isStrEq() 				const { return (isEq() && getChildrenSize() >= 2 && (getChild(0)->isVStr() || getChild(0)->isCStr() || getChild(0)->isStrOp())); };
        bool isStrComp() 			const { return (isStrLt() || isStrLe() || isStrGt() || isStrGe() || isStrEq()); };

        // check strings properties
        bool isStrInReg() 			const { return (kind == NODE_KIND::NT_STR_IN_REG); };
        bool isStrContains() 		const { return (kind == NODE_KIND::NT_STR_CONTAINS); };
        bool isStrIsDigit() 		const { return (kind == NODE_KIND::NT_STR_IS_DIGIT); };
        bool isStrProp() 			const { return (isStrInReg() || isStrContains() || isStrIsDigit()); };

        // check strings conversion
        bool isStrFromInt() 		const { return (kind == NODE_KIND::NT_STR_FROM_INT); };
        bool isStrToInt() 			const { return (kind == NODE_KIND::NT_STR_TO_INT); };
        bool isStrToReg() 			const { return (kind == NODE_KIND::NT_STR_TO_REG); };
        bool isStrToCode() 			const { return (kind == NODE_KIND::NT_STR_TO_CODE); };
        bool isStrFromCode() 		const { return (kind == NODE_KIND::NT_STR_FROM_CODE); };
        bool isStrConv() 			const { return (isStrFromInt() || isStrToInt() || isStrToReg() || isStrToCode() || isStrFromCode()); };

        // reg
        bool isRegNone() 			const { return (kind == NODE_KIND::NT_REG_NONE); };
        bool isRegAll() 			const { return (kind == NODE_KIND::NT_REG_ALL); };
        bool isRegAllChar() 		const { return (kind == NODE_KIND::NT_REG_ALLCHAR); };
        bool isRegConcat() 		    const { return (kind == NODE_KIND::NT_REG_CONCAT); };
        bool isRegUnion() 			const { return (kind == NODE_KIND::NT_REG_UNION); };
        bool isRegInter() 			const { return (kind == NODE_KIND::NT_REG_INTER); };
        bool isRegDiff() 			const { return (kind == NODE_KIND::NT_REG_DIFF); };
        bool isRegStar() 			const { return (kind == NODE_KIND::NT_REG_STAR); }; 
        bool isRegPlus() 			const { return (kind == NODE_KIND::NT_REG_PLUS); };
        bool isRegOpt() 			const { return (kind == NODE_KIND::NT_REG_OPT); };
        bool isRegRange() 			const { return (kind == NODE_KIND::NT_REG_RANGE); };
        bool isRegRepeat() 		    const { return (kind == NODE_KIND::NT_REG_REPEAT); };
        bool isRegLoop() 			const { return (kind == NODE_KIND::NT_REG_LOOP); };
        bool isRegComplement() 		const { return (kind == NODE_KIND::NT_REG_COMPLEMENT); };

        bool isAtom()				const { return (isArithComp() || isArithProp() ||
                                                    isBVCompOp() || 
                                                    isFPComp() || isFPProp() ||
                                                    isStrComp() || isStrProp() ||
                                                    (isApplyUF() && sort->isBool())); };
        // check let
        bool isLet()				const { return kind == NODE_KIND::NT_LET; };
        bool isLetChain()			const { return kind == NODE_KIND::NT_LET_CHAIN; };
        bool isLetBindVarList()		const { return kind == NODE_KIND::NT_LET_BIND_VAR_LIST; };

        // check ite
        bool isIte()				const { return kind == NODE_KIND::NT_ITE; };

        // check function
        bool isFuncDec()            const { return (kind == NODE_KIND::NT_FUNC_DEC); };
        bool isFuncDef()			const { return (kind == NODE_KIND::NT_FUNC_DEF); };
        bool isFuncParam()			const { return (kind == NODE_KIND::NT_FUNC_PARAM); };
        bool isFuncApply()          const { return (kind == NODE_KIND::NT_FUNC_APPLY); };

        // count the use of the node
        size_t getUseCount() const { return _use_count; };
        void incUseCount() { _use_count++; };
        void decUseCount() { _use_count--; };

        // get pure variable name for let bind var
        std::string getPureName()   const {
            if(isLetBindVar()){
                return name.substr(0, name.find(PRESERVING_LET_BIND_VAR_SUFFIX));
            }
            return name;
        }

        std::string toString()      const { return getPureName(); };

        // other functions
        /**
         * @brief Get the sort of the node
         * 
         * @return The sort of the node
         */
        std::shared_ptr<Sort> getSort()
                                    const { return sort; };
        /**
         * @brief Get the name of the node
         * 
         * @return The name of the node
         */
        std::string getName()       const { return name; };

        /**
         * @brief Get the re-named name of the node
         * 
         * @return The re-named name of the node
         */
        std::string rename(const std::string& new_name) {
            std::cerr << "Warning: rename " << name << " to " << new_name << std::endl;
            name = new_name;
            return new_name;
        }

        /**
         * @brief Get the kind of the node
         * 
         * @return The kind of the node
         */
        NODE_KIND getKind()           const { return kind; };

        /**
         * @brief Get the value of the node
         * 
         * @return The value of the node
         */
        std::shared_ptr<Value> getValue()           const { return value; };

        /**
         * @brief Set the value of the node
         * 
         * @param v The value to set
         */
        void setValue(std::shared_ptr<Value> v) { value = v; };

        void setValue(const Integer& v) { value = newValue(v); };

        void setValue(const Real& v) { value = newValue(v); };

        void setValue(const double& v) { value = newValue(v); };

        void setValue(const int& v) { value = newValue(v); };

        void setValue(const Interval& v) { value = newValue(v); };
        
        /**
         * @brief Get the number of children of the node
         * 
         * @return The number of children of the node
         */
        size_t getChildrenSize()    const { return children.size(); };

        /**
         * @brief Get the children of the node
         * 
         * @return The children of the node
         */
        std::vector<std::shared_ptr<DAGNode>> getChildren() 
                                    const { return children; };

        /**
         * @brief Get the child of the node
         * 
         * @param i The index of the child
         * @return The child of the node
         */
        std::shared_ptr<DAGNode> getChild(int i) 
                                    const { return children[i]; };
        // NOTE: function body is the first child

        /**
         * @brief Get the body of the function
         * 
         * @return The body of the function
         */
        std::shared_ptr<DAGNode> getFuncBody() 
                                    const { return children[0]; };

        /**
         * @brief Get the parameters of the function
         * 
         * @return The parameters of the function
         */
        std::vector<std::shared_ptr<DAGNode>> getFuncParams() const{
            std::vector<std::shared_ptr<DAGNode>> res;
            for(size_t i = 1;i<getChildrenSize();i++){
                res.emplace_back(getChild(i));
            }
            return res;
        }

        /**
         * @brief Get the number of parameters of the function
         * 
         * @return The number of parameters of the function
         */
        size_t getFuncParamsSize() const{
            return getChildrenSize() - 1;
        }

        // get quant body
        /**
         * @brief Get the body of the quantifier
         * 
         * @return The body of the quantifier
         */
        std::shared_ptr<DAGNode> getQuantBody() const { return children[0]; };

        /**
         * @brief Get the variables of the quantifier
         * 
         * @return The variables of the quantifier
         */
        std::vector<std::shared_ptr<DAGNode>> getQuantVars() const{
            std::vector<std::shared_ptr<DAGNode>> res;
            for(size_t i = 1;i<getChildrenSize();i++){
                res.emplace_back(getChild(i));
            }
            return res;
        }

        // is really equal to another node
        /**
         * @brief Check if the node is equivalent to another node
         * 
         * @param other The other node
         * @return True if the node is equivalent to the other node, false otherwise
         */
        bool isEquivalentTo(const std::shared_ptr<DAGNode>& other) const {
            return isEquivalentTo(*other);
        }

        /**
         * @brief Check if the node is equivalent to another node
         * 
         * @param other The other node
         * @return True if the node is equivalent to the other node, false otherwise
         */
        bool isEquivalentTo(const DAGNode& other) const {
            std::unordered_set<std::pair<const DAGNode*, const DAGNode*>, PairNodePtrHash, PairNodePtrEqual> visited;
            return isEquivalentTo(other, visited);
        }

        /**
         * @brief Get the hash code of the node
         * 
         * @return The hash code of the node
         */
        std::size_t hashCode() const{
            if(hash_computed) {
                return cached_hash_code;
            }
            
            // high quality hash algorithm, reduce conflicts
            size_t h1 = reinterpret_cast<size_t>(sort.get()); // Sort pointer, avoid string hash
            size_t h2 = static_cast<size_t>(kind);
            size_t h3 = name.empty() ? 0 : std::hash<std::string>{}(name);
            size_t h4 = children.size();
            size_t h5 = children_hash.empty() ? 0 : std::hash<std::string>{}(children_hash);
            
            // use better hash combination algorithm (based on boost::hash_combine)
            size_t seed = 0;
            seed ^= h1 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= h2 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= h3 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= h4 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            seed ^= h5 + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            
            seed ^= 0x9e3779b9 + (seed << 6) + (seed >> 2);
            
            cached_hash_code = seed;
            hash_computed = true;
            return cached_hash_code;
        }

        /**
         * @brief Update the function definition
         * 
         * @note This function is only used to update the function definition.
         * 
         * @param out_sort The output sort
         * @param body The body of the function
         * @param params The parameters of the function
         */
        void updateFuncDef(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params);

        /**
         * @brief Update the function application
         *
         * @note This function is only used to update the function application.
         * 
         * @param out_sort The output sort
         * @param body The body of the function
         * @param params The parameters of the function
         */
        void updateApplyFunc(std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body, const std::vector<std::shared_ptr<DAGNode>> &params);

    private:
        bool isEquivalentTo(const DAGNode& other, std::unordered_set<std::pair<const DAGNode*, const DAGNode*>, PairNodePtrHash, PairNodePtrEqual>& visited) const {
            TIME_FUNC();
            
            // fastest check: pointer same
            if (this == &other) {
                return true;
            }
            
            // fast structure check (avoid the expensive subsequent comparison)
            if (kind != other.kind || 
                children.size() != other.children.size() || 
                sort.get() != other.sort.get()) {
                return false;
            }
            
            // name check
            if (name != other.name) {
                return false;
            }
            
            // children_hash check (if both are calculated, this is the fastest deep comparison)
            if (!children_hash.empty() && !other.children_hash.empty() && 
                children_hash != other.children_hash) {
                return false;
            }
            
            auto p = std::make_pair(this, &other);
            if(visited.find(p) != visited.end()){
                return true;
            }
            visited.insert(p);
            
            // most expensive recursive comparison at the end
            for (size_t i = 0; i < children.size(); i++) {
                if (!children[i]->isEquivalentTo(*other.children[i], visited)) {
                    return false;
                }
            }
            return true;
        }
    };

    struct NodeHash {
        size_t operator()(const std::shared_ptr<DAGNode>& node) const {
            return node->hashCode();  // directly use the cached hash code
        }
    };

    struct NodeEqual {
        bool operator()(const std::shared_ptr<DAGNode>& node1, const std::shared_ptr<DAGNode>& node2) const {
            // fast path: first compare hash code
            if(node1->hashCode() != node2->hashCode()) {
                return false;
            }
            // only check the expensive equivalence when the hash is the same
            return node1->isEquivalentTo(*node2);
        }
    };

    std::string dumpSMTLIB2(const std::shared_ptr<DAGNode>& node);
    std::string dumpFuncDef(const std::shared_ptr<DAGNode>& node);
    std::string dumpFuncDec(const std::shared_ptr<DAGNode>& node);
    
    // smart pointer
    typedef std::shared_ptr<DAGNode> NodePtr;

    class NodeManager{
        private:
            std::vector<std::shared_ptr<DAGNode>> nodes;
            // use secondary hash: Kind -> Hash -> NodeIndex
            std::array<std::unordered_map<size_t, std::vector<std::pair<std::shared_ptr<DAGNode>, size_t>>>, NUM_KINDS> node_buckets;
        public:
            NodeManager();
            ~NodeManager();
            std::shared_ptr<DAGNode> getNode(const size_t index) const;
            size_t getIndex(const std::shared_ptr<DAGNode>& node) const;
            size_t size() const;

            // createNode methods corresponding to DAGNode constructors
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name, std::vector<std::shared_ptr<DAGNode>> children);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, NODE_KIND kind, std::string name);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, NODE_KIND kind);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort);
            std::shared_ptr<DAGNode> createNode();
            std::shared_ptr<DAGNode> createNode(NODE_KIND kind, std::string name);
            std::shared_ptr<DAGNode> createNode(NODE_KIND kind);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, const Integer& v);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, const Real& v);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, const double& v);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, const int& v);
            std::shared_ptr<DAGNode> createNode(std::shared_ptr<Sort> sort, const bool& v);
            std::shared_ptr<DAGNode> createNode(const std::string& n);
            
            void clear();
            
            // Getter functions for static constant nodes
            static std::shared_ptr<DAGNode> getNull() { return NULL_NODE; }
            static std::shared_ptr<DAGNode> getUnknown() { return UNKNOWN_NODE; }
            static std::shared_ptr<DAGNode> getTrue() { return TRUE_NODE; }
            static std::shared_ptr<DAGNode> getFalse() { return FALSE_NODE; }
            static std::shared_ptr<DAGNode> getE() { return E_NODE; }
            static std::shared_ptr<DAGNode> getPi() { return PI_NODE; }
            static std::shared_ptr<DAGNode> getNaN() { return NAN_NODE; }
            static std::shared_ptr<DAGNode> getEpsilon() { return EPSILON_NODE; }
            static std::shared_ptr<DAGNode> getPosEpsilon() { return POS_EPSILON_NODE; }
            static std::shared_ptr<DAGNode> getNegEpsilon() { return NEG_EPSILON_NODE; }
            
            // Infinity getters
            static std::shared_ptr<DAGNode> getStrInf() { return STR_INF_NODE; }
            static std::shared_ptr<DAGNode> getStrPosInf() { return STR_POS_INF_NODE; }
            static std::shared_ptr<DAGNode> getStrNegInf() { return STR_NEG_INF_NODE; }
            static std::shared_ptr<DAGNode> getIntInf() { return INT_INF_NODE; }
            static std::shared_ptr<DAGNode> getIntPosInf() { return INT_POS_INF_NODE; }
            static std::shared_ptr<DAGNode> getIntNegInf() { return INT_NEG_INF_NODE; }
            static std::shared_ptr<DAGNode> getRealInf() { return REAL_INF_NODE; }
            static std::shared_ptr<DAGNode> getRealPosInf() { return REAL_POS_INF_NODE; }
            static std::shared_ptr<DAGNode> getRealNegInf() { return REAL_NEG_INF_NODE; }
        public:
            // static constant nodes
            static const std::shared_ptr<DAGNode> NULL_NODE;
            static const std::shared_ptr<DAGNode> UNKNOWN_NODE;
            static const std::shared_ptr<DAGNode> TRUE_NODE;
            static const std::shared_ptr<DAGNode> FALSE_NODE;
            static const std::shared_ptr<DAGNode> E_NODE;
            static const std::shared_ptr<DAGNode> PI_NODE;
            // static const std::shared_ptr<DAGNode> INF_NODE;
            // static const std::shared_ptr<DAGNode> POS_INF_NODE;
            // static const std::shared_ptr<DAGNode> NEG_INF_NODE;
            static const std::shared_ptr<DAGNode> NAN_NODE;
            static const std::shared_ptr<DAGNode> EPSILON_NODE;
            static const std::shared_ptr<DAGNode> POS_EPSILON_NODE;
            static const std::shared_ptr<DAGNode> NEG_EPSILON_NODE;
            
            // infinity
            static const std::shared_ptr<DAGNode> STR_INF_NODE;
            static const std::shared_ptr<DAGNode> STR_POS_INF_NODE;
            static const std::shared_ptr<DAGNode> STR_NEG_INF_NODE;
            static const std::shared_ptr<DAGNode> INT_INF_NODE;
            static const std::shared_ptr<DAGNode> INT_POS_INF_NODE;
            static const std::shared_ptr<DAGNode> INT_NEG_INF_NODE;
            static const std::shared_ptr<DAGNode> REAL_INF_NODE;
            static const std::shared_ptr<DAGNode> REAL_POS_INF_NODE;
            static const std::shared_ptr<DAGNode> REAL_NEG_INF_NODE;
        private:
            void initializeStaticNodes();
            std::shared_ptr<DAGNode> insertNodeToBucket(const std::shared_ptr<DAGNode>& node);
    };

}
#endif