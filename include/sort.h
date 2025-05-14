/* -*- Header -*-
 *
 * The Sort Class
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

#ifndef _SORT_H
#define _SORT_H

#include "kind.h"
#include <vector>
#include <string>
#include <memory>

namespace SMTLIBParser{
    
    // supported const/variable types
    enum class SORT_KIND {
        SK_NULL=0, SK_UNKNOWN, SK_BOOL, SK_INT, SK_REAL, SK_BV, SK_FP, SK_STR, SK_ARRAY, SK_DATATYPE, SK_SET, SK_RELATION, SK_BAG, SK_SEQ, SK_UF, 
        SK_REG, // regular expression
        SK_EXT, // extended real
        SK_RAT, // rational number
        SK_NAT, // natural number
        SK_RAND, // random number
        SK_INTOREAL, // int or real, for constant
        SK_DEC, // declare-sort 
        SK_DEF  // define-sort
    };

    class Sort{
    public:
        SORT_KIND kind;
        std::string name;
        size_t arity;
        std::vector<std::shared_ptr<Sort>> children;
        Sort(SORT_KIND kind, std::string name, size_t arity, std::vector<std::shared_ptr<Sort>> children): kind(kind), name(name), arity(arity), children(children) {}
        Sort(SORT_KIND kind, std::string name, size_t arity): kind(kind), name(name), arity(arity) {}
        Sort(SORT_KIND kind, std::string name): kind(kind), name(name), arity(0) {}
        Sort(SORT_KIND kind): kind(kind), name(""), arity(0) {}
        Sort(std::string name): kind(SORT_KIND::SK_UNKNOWN), name(name), arity(0) {}
        Sort(): kind(SORT_KIND::SK_UNKNOWN), name(""), arity(0) {}
        Sort(const Sort& other): kind(other.kind), name(other.name), arity(other.arity), children(other.children) {}


        // check the type of the sort
        bool isNull() const { return kind == SORT_KIND::SK_NULL; }
        bool isUnknown() const { return kind == SORT_KIND::SK_UNKNOWN; }
        bool isBool() const { return kind == SORT_KIND::SK_BOOL; }
        bool isIntOrReal() const { return kind == SORT_KIND::SK_INTOREAL || kind == SORT_KIND::SK_INT || kind == SORT_KIND::SK_REAL; }
        bool isInt() const { return kind == SORT_KIND::SK_INT; }
        bool isReal() const { return kind == SORT_KIND::SK_REAL; }
        bool isBv() const { return kind == SORT_KIND::SK_BV; }
        bool isFp() const { return kind == SORT_KIND::SK_FP; }
        bool isStr() const { return kind == SORT_KIND::SK_STR; }
        bool isReg() const { return kind == SORT_KIND::SK_REG; }
        bool isExt() const { return kind == SORT_KIND::SK_EXT; }
        bool isArray() const { return kind == SORT_KIND::SK_ARRAY; }
        bool isDatatype() const { return kind == SORT_KIND::SK_DATATYPE; }
        bool isSet() const { return kind == SORT_KIND::SK_SET; }
        bool isRelation() const { return kind == SORT_KIND::SK_RELATION; }
        bool isBag() const { return kind == SORT_KIND::SK_BAG; }
        bool isSeq() const { return kind == SORT_KIND::SK_SEQ; }
        bool isUF() const { return kind == SORT_KIND::SK_UF; }
        bool isRat() const { return kind == SORT_KIND::SK_RAT; }
        bool isNat() const { return kind == SORT_KIND::SK_NAT; }
        bool isRand() const { return kind == SORT_KIND::SK_RAND; }
        bool isDec() const { return kind == SORT_KIND::SK_DEC; }
        bool isDef() const { return kind == SORT_KIND::SK_DEF; }

        // compare two sorts
        bool operator==(const Sort& other) const {
            if(((isInt() || isReal()) && other.isIntOrReal()) || (isIntOrReal() && (other.isInt() || other.isReal()))){
                return true;
            }
            else if((isReal() && other.isRat()) || (isRat() && other.isReal())){
                return true;
            }
            return kind == other.kind && name == other.name && arity == other.arity;
        }
        bool operator!=(const Sort& other) const {
            return !(*this == other);
        }

        // print the sort
        std::string toString() const {
            switch (kind) {
                case SORT_KIND::SK_BOOL: return "Bool";
                case SORT_KIND::SK_INT: return "Int";
                case SORT_KIND::SK_REAL: return "Real";
                case SORT_KIND::SK_BV:
                    return "(_ BitVec " + std::to_string(children[0]->arity) + ")";
                case SORT_KIND::SK_FP:
                    return "(_ FloatingPoint " + std::to_string(children[0]->arity) + " " + std::to_string(children[1]->arity) + ")";
                case SORT_KIND::SK_STR: return "String";
                case SORT_KIND::SK_ARRAY: return "(Array " + children[0]->toString() + " " + children[1]->toString() + ")";
                case SORT_KIND::SK_DATATYPE: return "Datatype";
                case SORT_KIND::SK_SET: return "Set";
                case SORT_KIND::SK_RELATION: return "Relation";
                case SORT_KIND::SK_BAG: return "Bag";
                case SORT_KIND::SK_SEQ: return "Sequence";
                case SORT_KIND::SK_UF: return "UF";
                case SORT_KIND::SK_REG: return "RegLan";
                case SORT_KIND::SK_EXT: return "ExtReal";
                case SORT_KIND::SK_RAT: return "Rational";
                case SORT_KIND::SK_NAT: return "Natural";
                case SORT_KIND::SK_RAND: return "Random";
                case SORT_KIND::SK_INTOREAL: return "IntOrReal";
                default: return "Unknown";
            }
        }

        size_t getBitWidth() const {
            assert(kind == SORT_KIND::SK_BV);
            return children[0]->arity;
        }

        size_t getExponentWidth() const {
            assert(kind == SORT_KIND::SK_FP);
            return children[0]->arity;
        }

        size_t getSignificandWidth() const {
            assert(kind == SORT_KIND::SK_FP);
            return children[1]->arity;
        }

        std::shared_ptr<Sort> getIndexSort() const {
            assert(kind == SORT_KIND::SK_ARRAY);
            return children[0];
        }

        std::shared_ptr<Sort> getElemSort() const {
            assert(kind == SORT_KIND::SK_ARRAY);
            return children[1];
        }
        
        bool isEqTo(const Sort& other) const {
            return *this == other;
        }

        bool isEqTo(const std::shared_ptr<Sort>& other) const {
            return *this == *other;
        }
    };
    
    inline const std::shared_ptr<Sort> NULL_SORT = std::make_shared<Sort>(SORT_KIND::SK_NULL, "Null", 0);
    inline const std::shared_ptr<Sort> UNKNOWN_SORT = std::make_shared<Sort>(SORT_KIND::SK_UNKNOWN, "Unknown", 0);
    inline const std::shared_ptr<Sort> BOOL_SORT = std::make_shared<Sort>(SORT_KIND::SK_BOOL, "Bool", 0);
    inline const std::shared_ptr<Sort> INT_SORT = std::make_shared<Sort>(SORT_KIND::SK_INT, "Int", 0);
    inline const std::shared_ptr<Sort> REAL_SORT = std::make_shared<Sort>(SORT_KIND::SK_REAL, "Real", 0);
    inline const std::shared_ptr<Sort> STR_SORT = std::make_shared<Sort>(SORT_KIND::SK_STR, "String", 0);
    inline const std::shared_ptr<Sort> REG_SORT = std::make_shared<Sort>(SORT_KIND::SK_REG, "Reg", 0);
    inline const std::shared_ptr<Sort> EXT_SORT = std::make_shared<Sort>(SORT_KIND::SK_EXT, "ExtReal", 0);
    inline const std::shared_ptr<Sort> RAT_SORT = std::make_shared<Sort>(SORT_KIND::SK_RAT, "Rational", 0);
    inline const std::shared_ptr<Sort> NAT_SORT = std::make_shared<Sort>(SORT_KIND::SK_NAT, "Natural", 0);
    inline const std::shared_ptr<Sort> RAND_SORT = std::make_shared<Sort>(SORT_KIND::SK_RAND, "Random", 0);
    inline const std::shared_ptr<Sort> INTOREAL_SORT = std::make_shared<Sort>(SORT_KIND::SK_INTOREAL, "IntOrReal", 0);

    std::shared_ptr<Sort> mkBVSort(size_t width);
    std::shared_ptr<Sort> mkFPSort(size_t exp, size_t sig);
    std::shared_ptr<Sort> mkArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem);
}
#endif