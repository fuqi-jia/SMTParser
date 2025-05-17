/* -*- Source -*-
 *
 * The Util Functions
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

#include "util.h"
#include <vector>
#include <sstream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <string>
namespace SMTLIBParser{

    // SHA-256 hash function
    std::string sha256(const std::string& input) {
        return SHA256::hash(input);
    }

    bool isIntUtil(const std::string& str){
        if (str.empty()) return false;
        for (size_t i = 0; i < str.size(); i++){
            if (i == 0 && (str[i] == '-' || str[i] == '+')) continue;
            if (!isdigit(str[i])) return false;
        }
        return true;

    }
    bool isRealUtil(const std::string& str){
        if (str.empty()) return false;
        bool has_dot = false;
        for (size_t i = 0; i < str.size(); i++){
            if (i == 0 && (str[i] == '-' || str[i] == '+')) continue;
            if (str[i] == '.' && !has_dot){
                has_dot = true;
                continue;
            }
            if (!isdigit(str[i])) return false;
        }
        return true;
    }

    bool isScientificNotationUtil(const std::string& str){
        if (str.empty()) return false;
        
        // find 'E' or 'e' character
        size_t e_pos = str.find_first_of("Ee");
        if (e_pos == std::string::npos || e_pos == 0) 
            return false;
            
        // check if the part before E is a valid real number
        std::string mantissa = str.substr(0, e_pos);
        if (!isRealUtil(mantissa)) 
            return false;
        
        // extract the part after E
        std::string exponent = str.substr(e_pos + 1);
        
        // if the exponent part is empty, not a valid scientific notation
        if (exponent.empty())
            return false;
        
        // create a copy without spaces for checking
        std::string exponent_no_spaces = exponent;
        exponent_no_spaces.erase(std::remove_if(exponent_no_spaces.begin(), exponent_no_spaces.end(), 
                                     [](unsigned char c) { return std::isspace(c); }), 
                      exponent_no_spaces.end());
        
        // if the exponent part is empty after removing spaces, not a valid scientific notation
        if (exponent_no_spaces.empty())
            return false;
        
        // handle possible parentheses
        if (exponent_no_spaces[0] == '(') {
            // find right parenthesis
            size_t close_pos = exponent_no_spaces.find(')');
            if (close_pos != std::string::npos) {
                // extract the content inside parentheses
                exponent_no_spaces = exponent_no_spaces.substr(1, close_pos - 1);
            } else {
                // no right parenthesis found, possibly incomplete expression
                exponent_no_spaces = exponent_no_spaces.substr(1);
            }
        }
        
        // if the exponent part is empty after handling parentheses, not a valid scientific notation
        if (exponent_no_spaces.empty())
            return false;
        
        // check if the exponent part is a valid integer
        if (exponent_no_spaces[0] == '+' || exponent_no_spaces[0] == '-') {
            // if "E-" or "E+", there must be a digit after it
            if (exponent_no_spaces.size() == 1) 
                return false;
            // check if the part after "E-" or "E+" is all digits
            for (size_t i = 1; i < exponent_no_spaces.size(); i++) {
                if (!isdigit(exponent_no_spaces[i])) 
                    return false;
            }
        } else {
            // if there is no sign, the whole exponent part must be all digits
            for (char c : exponent_no_spaces) {
                if (!isdigit(c)) 
                    return false;
            }
        }
        
        return true;
    }

    std::string parseScientificNotation(const std::string& str){
        // find 'E' or 'e' character
        size_t e_pos = str.find_first_of("Ee");
        if (e_pos == std::string::npos) 
            return str;
            
        try {
            // extract the mantissa part
            std::string mantissa = str.substr(0, e_pos);
            
            // check if the mantissa part is a valid real number
            if (!isRealUtil(mantissa))
                return str;
            
            // extract the exponent part
            std::string exponent = str.substr(e_pos + 1);
            
            // if the exponent part is empty, return the original string
            if (exponent.empty())
                return str;
            
            // create a copy without spaces for processing
            std::string exponent_no_spaces = exponent;
            exponent_no_spaces.erase(std::remove_if(exponent_no_spaces.begin(), exponent_no_spaces.end(), 
                                         [](unsigned char c) { return std::isspace(c); }), 
                          exponent_no_spaces.end());
            
            // if the exponent part is empty after removing spaces, return the original string
            if (exponent_no_spaces.empty())
                return str;
            
            // handle possible parentheses
            if (exponent_no_spaces[0] == '(') {
                // find right parenthesis
                size_t close_pos = exponent_no_spaces.find(')');
                if (close_pos != std::string::npos) {
                    // extract the content inside parentheses
                    exponent_no_spaces = exponent_no_spaces.substr(1, close_pos - 1);
                } else {
                    // no right parenthesis found, possibly incomplete expression
                    exponent_no_spaces = exponent_no_spaces.substr(1);
                }
            }
            
            // if the exponent part is empty after handling parentheses, return the original string
            if (exponent_no_spaces.empty())
                return str;
            
            // convert scientific notation to normal real number
            // TODO!!
            Real mantissa_val = Real(mantissa);
            Real exponent_val = Real(exponent_no_spaces);
            
            // calculate the result
            Real result = mantissa_val * SMTLIBParser::pow(Real(10.0), exponent_val);
            
            // convert to string
            std::ostringstream oss;
            oss << std::setprecision(16) << toString(result);
            return oss.str();
        } catch (const std::exception& e) {
            // conversion failed, return the original string
            return str;
        }
    }

    bool isBVUtil(const std::string& str){
        if (str.empty()) return false;
        if (str.size() < 3) return false;
        if (str[0] != '#') return false;
        if (str[1] != 'b' && str[1] != 'x' && str[1] != 'd' &&
            str[1] != 'B' && str[1] != 'X' && str[1] != 'D') return false;
        for (size_t i = 2; i < str.size(); i++){
            if ((str[1] == 'b' || str[1] == 'B') && 
                (str[i] != '0' && str[i] != '1')) return false;
            if ((str[1] == 'x' || str[1] == 'X') &&
                (str[i] != '0' && 
                str[i] != '1' && 
                str[i] != '2' && 
                str[i] != '3' && 
                str[i] != '4' && 
                str[i] != '5' && 
                str[i] != '6' && 
                str[i] != '7' && 
                str[i] != '8' && 
                str[i] != '9' && 
                str[i] != 'a' && 
                str[i] != 'A' && 
                str[i] != 'b' && 
                str[i] != 'B' && 
                str[i] != 'c' && 
                str[i] != 'C' && 
                str[i] != 'd' && 
                str[i] != 'D')) return false;
            if ((str[1] == 'd' || str[1] == 'D') && 
                (str[i] != '0' && 
                str[i] != '1' && 
                str[i] != '2' && 
                str[i] != '3' && 
                str[i] != '4' && 
                str[i] != '5' && 
                str[i] != '6' && 
                str[i] != '7' && 
                str[i] != '8' && 
                str[i] != '9')) return false;
        }
        return true;
    }
    bool isFPUtil(const std::string& str){
        if (str.empty()) return false;
        if (str.size() < 3) return false;
        if (str[0] != '#' || str[1] != 'x') return false;
        for (size_t i = 2; i < str.size(); i++){
            if (!isxdigit(str[i])) return false;
        }
        return true;
    }
    bool isStrUtil(const std::string& str){
        if (str.empty()) return false;
        if (str[0] != '"' || str[str.size()-1] != '"') return false;
        return true;
    }


    Integer pow(const Integer& base, const Integer& exp){
        if(exp == 0) return 1;
        Integer result = base;
        for(Integer i = 1; i < exp; i++){
            result *= base;
        }
        return result;
    }
    Real pow(const Real& base, const Real& exp){
        return base.pow(exp);
    }

    Integer gcd(const Integer& a, const Integer& b){
        if(b == 0) return a;
        return gcd(b, a % b);
    }

    Integer lcm(const Integer& a, const Integer& b){
        return a * b / SMTLIBParser::gcd(a, b);
    }


    Real sqrt(const Integer& i){
        if(i < 0){
            std::cerr << "Error: sqrt of negative number" << std::endl;
            exit(1);
        }
        return HighPrecisionReal(i).sqrt();
    }
    Real sqrt(const Real& r){
        if(r < 0){
            std::cerr << "Error: sqrt of negative number" << std::endl;
            exit(1);
        }
        return r.sqrt();
    }

    Real safesqrt(const Integer& i){
        if(i < 0){
            return Real(0);
        }
        return HighPrecisionReal(i).sqrt();
    }
    
    Real safesqrt(const Real& r){
        if(r < 0){
            return Real(0);
        }
        return r.sqrt();
    }

    Integer ceil(const Real& r){
        return r.ceil().toInteger();
    }
    Integer floor(const Real& r){
        return r.floor().toInteger();
    }
    Integer round(const Real& r){
        return r.round().toInteger();
    }

    bool isPrime(const Integer& n){
        if(n <= 1) return false;
        if(n == 2) return true;
        if(n % 2 == 0) return false;
        for(Integer i = 3; i * i <= n; i += 2){
            if(n % i == 0) return false;
        }
        return true;
    }

    bool isEven(const Integer& n){
        return n % 2 == 0;
    }

    bool isOdd(const Integer& n){
        return n % 2 != 0;
    }


    Integer factorial(const Integer& n){
        Integer res = 1;
        for(Integer i = 1; i <= n; i++){
            res *= i;
        }
        return res;
    }

    std::string bvNot(const std::string& bv){
        assert(bv[0] == '#' && bv[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv.size(); i++){
            res += bv[i] == '0' ? '1' : '0';
        }
        return res;
    }
    std::string bvAnd(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] == '1' && bv2[i] == '1' ? '1' : '0';
        }
        return res;
    }
    std::string bvOr(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] == '1' || bv2[i] == '1' ? '1' : '0';
        }
        return res;
    }
    std::string bvXor(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] != bv2[i] ? '1' : '0';
        }
        return res;
    }
    std::string bvNand(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] == '1' && bv2[i] == '1' ? '0' : '1';
        }
        return res;
    }
    std::string bvNor(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] == '0' && bv2[i] == '0' ? '1' : '0';
        }
        return res;
    }
    std::string bvXnor(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = "#b";
        for(size_t i = 2; i < bv1.size(); i++){
            res += bv1[i] == bv2[i] ? '1' : '0';
        }
        return res;
    }

    std::string bvNeg(const std::string& bv){
        assert(bv[0] == '#' && bv[1] == 'b');
        // 2's complement
        std::string res = "";
        bool carry = true;
        for(size_t i = bv.size() - 1; i >= 2; i--){
            if(bv[i] == '0'){
                res += carry ? '1' : '0';
                carry = false;
            }
            else{
                res += carry ? '0' : '1';
            }
        }
        res = std::string(res.rbegin(), res.rend());
        res = "#b" + res;
        return res;
    }

    std::string bvAdd(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string bv1_ = bv1.substr(2, bv1.size() - 2);
        std::string bv2_ = bv2.substr(2, bv2.size() - 2);
        if(bv1_.size() != bv2_.size()){
            // add prefix 0 to the shorter one
            if(bv1_.size() < bv2_.size()){
                bv1_ = "#b" + std::string(bv2_.size() - bv1_.size(), '0') + bv1_;
                bv2_ = "#b" + bv2_;
            }
            else{
                bv2_ = "#b" + std::string(bv1_.size() - bv2_.size(), '0') + bv2_;
                bv1_ = "#b" + bv1_;
            }
        }
        else{
            bv1_ = "#b" + bv1_;
            bv2_ = "#b" + bv2_;
        }   
        std::string res = "";
        bool carry = false;
        for(size_t i = bv1_.size() - 1; i >= 2; i--){
            if(bv1_[i] == '0' && bv2_[i] == '0'){
                res += carry ? '1' : '0';
                carry = false;
            }
            else if(bv1_[i] == '1' && bv2_[i] == '1'){
                res += carry ? '1' : '0';
                carry = true;
            }
            else{
                res += carry ? '0' : '1';
            }
        }
        // add #b prefix and reverse
        res = std::string(res.rbegin(), res.rend());
        res = "#b" + res;
        return res;
    }
    std::string bvSub(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string bv1_ = bv1.substr(2, bv1.size() - 2);
        std::string bv2_ = bv2.substr(2, bv2.size() - 2);
        if(bv1_.size() != bv2_.size()){
            // add prefix 0 to the shorter one
            if(bv1_.size() < bv2_.size()){
                bv1_ = "#b" + std::string(bv2_.size() - bv1_.size(), '0') + bv1_;
                bv2_ = "#b" + bv2_;
            }
            else{
                bv2_ = "#b" + std::string(bv1_.size() - bv2_.size(), '0') + bv2_;
                bv1_ = "#b" + bv1_;
            }
        }
        else{
            bv1_ = "#b" + bv1_;
            bv2_ = "#b" + bv2_;
        }
        std::string res = "";
        bool borrow = false;
        for(size_t i = bv1_.size() - 1; i >= 2; i--){
            if(bv1_[i] == '0' && bv2_[i] == '0'){
                res += borrow ? '1' : '0';
                borrow = false;
            }
            else if(bv1_[i] == '1' && bv2_[i] == '1'){
                res += borrow ? '0' : '1';
                borrow = true;
            }
            else{
                res += borrow ? '1' : '0';
            }
        }
        res = std::string(res.rbegin(), res.rend());
        res = "#b" + res;
        return res;
    }
    std::string bvMul(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string bv1_ = bv1.substr(2, bv1.size() - 2);
        std::string bv2_ = bv2.substr(2, bv2.size() - 2);
        if(bv1_.size() != bv2_.size()){
            // add prefix 0 to the shorter one
            if(bv1_.size() < bv2_.size()){
                bv1_ = "#b" + std::string(bv2_.size() - bv1_.size(), '0') + bv1_;
                bv2_ = "#b" + bv2_;
            }
            else{
                bv2_ = "#b" + std::string(bv1_.size() - bv2_.size(), '0') + bv2_;
                bv1_ = "#b" + bv1_;
            }
        }
        else{
            bv1_ = "#b" + bv1_;
            bv2_ = "#b" + bv2_;
        }
        std::vector<std::string> partials;
        for(int i = bv2_.size() - 1; i >= 0; i--){
            if(bv2_[i] == '1'){
                std::string partial = bv1_.substr(0, bv2_.size() - i);
                partial = partial + std::string(i - 1, '0');
                partial = "#b" + partial;
                partials.push_back(partial);
            }
        }
        if(partials.empty()){
            return "#b" + std::string(bv1_.size() - 2, '0');
        }
        std::string res = partials[0];
        for(size_t i = 1; i < partials.size(); i++){
            res = SMTLIBParser::bvAdd(res, partials[i]);
        }
        return res;
    }


    std::string bvUdiv(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');

        // div 0, return all ones
        bool isBv2Zero = true;
        for(size_t i = 2; i < bv2.size(); i++){
            if(bv2[i] == '1'){
                isBv2Zero = false;
                break;
            }
        }
        if(isBv2Zero){
            return "#b" + std::string(bv1.size() - 2, '1');
        }

        std::string bv1_ = bv1.substr(2, bv1.size() - 2);
        std::string bv2_ = bv2.substr(2, bv2.size() - 2);
        if(bv1_.size() != bv2_.size()){
            // add prefix 0 to the shorter one
            if(bv1_.size() < bv2_.size()){
                bv1_ = "#b" + std::string(bv2_.size() - bv1_.size(), '0') + bv1_;
                bv2_ = "#b" + bv2_;
            }
            else{
                bv2_ = "#b" + std::string(bv1_.size() - bv2_.size(), '0') + bv2_;
                bv1_ = "#b" + bv1_;
            }
        }
        else{
            bv1_ = "#b" + bv1_;
            bv2_ = "#b" + bv2_;
        }
        // special case: divide by 0
        bool isZero = true;
        for(size_t i = 2; i < bv2_.size(); i++){
            if(bv2_[i] == '1'){
                isZero = false;
                break;
            }
        }
        if(isZero){
            // divide by 0, return all ones
            return "#b" + std::string(bv1.size() - 2, '1');
        }
        
        // extract pure binary bits (without #b prefix)
        std::string dividend_bits = bv1_.substr(2);
        std::string divisor_bits = bv2_.substr(2);
        
        std::string quotient_bits;
        std::string remainder = "";
        
        // long division
        for(char bit : dividend_bits){
            // add current bit to remainder
            remainder.push_back(bit);
            
            // try division
            if(remainder.length() < divisor_bits.length()){
                // remainder length not enough, add 0 to quotient
                quotient_bits.push_back('0');
            }
            else{
                // compare remainder with divisor (need to add #b prefix for comparison)
                std::string remainder_bv = "#b" + remainder;
                std::string divisor_bv = "#b" + divisor_bits;
                
                // binary string comparison
                bool geq = true;
                if(remainder.length() != divisor_bits.length()){
                    geq = remainder.length() > divisor_bits.length();
                }
                else{
                    for(size_t i = 0; i < remainder.length(); i++){
                        if(remainder[i] < divisor_bits[i]){
                            geq = false;
                            break;
                        }
                        else if(remainder[i] > divisor_bits[i]){
                            break;
                        }
                    }
                }
                
                if(geq){
                    // remainder greater than or equal to divisor, add 1 to quotient
                    quotient_bits.push_back('1');
                    
                    // subtract divisor from remainder
                    std::string diff = SMTLIBParser::bvSub(remainder_bv, divisor_bv);
                    remainder = diff.substr(2); // remove #b prefix
                }
                else{
                    // remainder less than divisor, add 0 to quotient
                    quotient_bits.push_back('0');
                }
            }
        }
        
        // return result with prefix
        return "#b" + quotient_bits;
    }
    std::string bvUrem(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        // div 0, return first operand
        bool isZero = true;
        for(size_t i = 2; i < bv2.size(); i++){
            if(bv2[i] == '1'){
                isZero = false;
                break;
            }
        }
        if(isZero){
            return bv1;
        }
        std::string dividend = bv1;
        std::string divisor = bv2;
        std::string quotient = SMTLIBParser::bvUdiv(bv1, bv2);
        std::string res = SMTLIBParser::bvSub(dividend, SMTLIBParser::bvMul(quotient, bv2));
        return res;
    }
    std::string bvUmod(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        std::string res = SMTLIBParser::bvUrem(bv1, bv2);
        return res;
    }
    std::string bvSdiv(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        bool isNeg1 = bv1[2] == '1';
        bool isNeg2 = bv2[2] == '1';
        // div 0, return all ones if positive, otherwise 1
        bool isZero = true;
        for(size_t i = 2; i < bv2.size(); i++){
            if(bv2[i] == '1'){
                isZero = false;
                break;
            }
        }
        if(isZero){
            if(isNeg1){
                return "#b" + std::string(bv1.size() - 3, '0') + "1";
            }
            else{
                return "#b" + std::string(bv1.size() - 2, '0') + "1";
            }
        }
        std::string res = SMTLIBParser::bvUdiv(bv1, bv2);
        if(isNeg1 ^ isNeg2){
            res = SMTLIBParser::bvNot(res);
            res = SMTLIBParser::bvAdd(res, "#b01");
        }
        return res;
    }
    std::string bvSrem(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        // rem 0, return first operand
        bool isZero = true;
        for(size_t i = 2; i < bv2.size(); i++){
            if(bv2[i] == '1'){
                isZero = false;
                break;
            }
        }
        if(isZero){
            return bv1;
        }
        bool isNeg1 = bv1[2] == '1';
        std::string res = SMTLIBParser::bvUrem(bv1, bv2);
        if(isNeg1){
            res = SMTLIBParser::bvNot(res);
            res = SMTLIBParser::bvAdd(res, "#b01");
        }
        return res;
    }
    std::string bvSmod(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        bool isNeg1 = bv1[2] == '1';
        std::string res = SMTLIBParser::bvSrem(bv1, bv2);
        if(isNeg1){
            res = SMTLIBParser::bvNot(res);
            res = SMTLIBParser::bvAdd(res, "#b01");
        }
        return res;
    }

    std::string bvShl(const std::string& bv, const std::string& n){
        // left shift
        assert(bv[0] == '#' && bv[1] == 'b');
        assert(n[0] == '#' && n[1] == 'b');
        size_t shift = Integer(n.substr(2, n.size() - 2)).toULong();
        if(shift >= bv.size() - 2){
            return "#b0" + std::string(shift - bv.size() + 2, '0');
        }
        else{
            return "#b" + bv.substr(2, bv.size() - 2 - shift) + std::string(shift, '0');
        }
    }
    std::string bvLshr(const std::string& bv, const std::string& n){
        // logical right shift
        assert(bv[0] == '#' && bv[1] == 'b');
        assert(n[0] == '#' && n[1] == 'b');
        size_t shift = Integer(n.substr(2, n.size() - 2)).toULong();
        if(shift >= bv.size() - 2){
            return "#b0" + std::string(shift - bv.size() + 2, '0');
        }
        else{
            return "#b" + std::string(shift, '0') + bv.substr(2, bv.size() - 2 - shift);
        }
    }
    std::string bvAshr(const std::string& bv, const std::string& n){
        // arithmetic right shift
        assert(bv[0] == '#' && bv[1] == 'b');
        assert(n[0] == '#' && n[1] == 'b');
        size_t shift = Integer(n.substr(2, n.size() - 2)).toULong();
        if(shift >= bv.size() - 2){
            return "#b" + std::string(bv.size() - 2, bv[2]);
        }
        else{
            return "#b" + std::string(shift, bv[2]) + bv.substr(2, bv.size() - 2 - shift);
        }
    }

    std::string bvConcat(const std::string& bv1, const std::string& bv2){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        return "#b" + bv1.substr(2, bv1.size() - 2) + bv2.substr(2, bv2.size() - 2);
    }
    std::string bvExtract(const std::string& bv, const Integer& i, const Integer& j){
        assert(bv[0] == '#' && bv[1] == 'b');
        assert(i >= j);
        return "#b" + bv.substr(2 + bv.size() - 2 - j.toULong(), i.toULong() - j.toULong() + 1);
    }
    std::string bvRepeat(const std::string& bv, const Integer& n){
        assert(bv[0] == '#' && bv[1] == 'b');
        std::string res = "";
        for(size_t i = 0; i < n.toULong(); i++){
            res += bv.substr(2, bv.size() - 2);
        }
        return "#b" + res;
    }
    std::string bvZeroExtend(const std::string& bv, const Integer& n){
        assert(bv[0] == '#' && bv[1] == 'b');
        return "#b" + std::string(n.toULong(), '0') + bv.substr(2, bv.size() - 2);
    }
    std::string bvSignExtend(const std::string& bv, const Integer& n){
        assert(bv[0] == '#' && bv[1] == 'b');
        return "#b" + std::string(n.toULong(), bv[2]) + bv.substr(2, bv.size() - 2);
    }

    std::string bvRotateLeft(const std::string& bv, const Integer& n){
        assert(bv[0] == '#' && bv[1] == 'b');
        Integer real_n = n % (bv.size() - 2);
        return "#b" + bv.substr(2 + n.toULong(), bv.size() - 2 - n.toULong()) + bv.substr(2, n.toULong());
    }
    std::string bvRotateRight(const std::string& bv, const Integer& n){
        assert(bv[0] == '#' && bv[1] == 'b');
        Integer real_n = n % (bv.size() - 2);
        return "#b" + bv.substr(2 + bv.size() - 2 - n.toULong(), n.toULong()) + bv.substr(2, bv.size() - 2 - n.toULong());
    }

    bool bvComp(const std::string& bv1, const std::string& bv2, const NODE_KIND& kind){
        assert(bv1[0] == '#' && bv1[1] == 'b');
        assert(bv2[0] == '#' && bv2[1] == 'b');
        switch(kind){
            case NODE_KIND::NT_BV_COMP:
                return bv1 == bv2;
            case NODE_KIND::NT_EQ_OTHER:
                return bv1 == bv2;
            case NODE_KIND::NT_DISTINCT_OTHER:
                return bv1 != bv2;
            case NODE_KIND::NT_BV_ULT:
                return SMTLIBParser::bvToNat(bv1) < SMTLIBParser::bvToNat(bv2);
            case NODE_KIND::NT_BV_ULE:
                return SMTLIBParser::bvToNat(bv1) <= SMTLIBParser::bvToNat(bv2);
            case NODE_KIND::NT_BV_UGT:
                return SMTLIBParser::bvToNat(bv1) > SMTLIBParser::bvToNat(bv2);
            case NODE_KIND::NT_BV_UGE:
                return SMTLIBParser::bvToNat(bv1) >= SMTLIBParser::bvToNat(bv2);
            case NODE_KIND::NT_BV_SLT:
                return SMTLIBParser::bvToInt(bv1) < SMTLIBParser::bvToInt(bv2);
            case NODE_KIND::NT_BV_SLE:
                return SMTLIBParser::bvToInt(bv1) <= SMTLIBParser::bvToInt(bv2);
            case NODE_KIND::NT_BV_SGT:
                return SMTLIBParser::bvToInt(bv1) > SMTLIBParser::bvToInt(bv2);
            case NODE_KIND::NT_BV_SGE:
                return SMTLIBParser::bvToInt(bv1) >= SMTLIBParser::bvToInt(bv2);
            default:
                return false;
        }
    }

    std::string bvToNat(const std::string& bv){
        assert(bv[0] == '#' && bv[1] == 'b');
        Integer res = 0;
        for(size_t i = 2; i < bv.size(); i++){
            res = res * 2 + (bv[i] == '1' ? 1 : 0);
        }
        return res.toString();
    }
    std::string natToBv(const Integer& i, const Integer& n){
        std::string res = "#b";
        std::string bin = i.toString(2);
        if(bin.size() < n.toULong()){
            res += std::string(n.toULong() - bin.size(), '0') + bin;
        }
        else{
            res += bin.substr(bin.size() - n.toULong(), n.toULong());
        }
        return res;
    }
    std::string hexToBv(const std::string& hex){
        std::string res = "#b";
        for(size_t i = 0; i < hex.size(); i++){
            switch(hex[i]){
                case '0':
                    res += "0000";
                    break;
                case '1':
                    res += "0001";
                    break;
                case '2':
                    res += "0010";
                    break;
                case '3':
                    res += "0011";
                    break;
                case '4':
                    res += "0100";
                    break;
                case '5':
                    res += "0101";
                    break;
                case '6':
                    res += "0110";
                    break;
                case '7':
                    res += "0111";
                    break;
                case '8':
                    res += "1000";
                    break;
                case '9':
                    res += "1001";
                    break;
                case 'a':
                    res += "1010";
                    break;
                case 'A':
                    res += "1010";
                    break;
                case 'b':
                    res += "1011";
                    break;
                case 'B':
                    res += "1011";
                    break;
                case 'c':
                    res += "1100";
                    break;
                case 'C':
                    res += "1100";
                    break;
                case 'd':
                    res += "1101";
                    break;
                case 'D':
                    res += "1101";
                    break;
                case 'e':
                    res += "1110";
                    break;
                case 'E':
                    res += "1110";
                    break;
                case 'f':
                    res += "1111";
                    break;
                case 'F':
                    res += "1111";
                    break;
                default:
                    assert(false);
            }
        }
        return res;
    }
    std::string decToBv(const std::string& dec){
        std::string res = "#b";
        Integer i = Integer(dec);
        std::string bin = i.toString(2);
        return res + bin;
    }
    
    std::string natToBv(const std::string& i, const Integer& n){
        if(i.size() > 2 && i[0] == '#' && i[1] == 'b'){
            // zero-extend
            std::string res = "#b";
            std::string bin = i.substr(2, i.size() - 2);
            if(bin.size() < n.toULong()){
                res += std::string(n.toULong() - bin.size(), '0') + bin;
            }
            else{
                res += bin.substr(bin.size() - n.toULong(), n.toULong());
            }
            return res;
        }
        else if(i.size() > 2 && i[0] == '#' && i[1] == 'x'){
            // #x -> #b
            return hexToBv(i.substr(2, i.size() - 2));
        }
        else if(i.size() > 2 && i[0] == '#' && i[1] == 'd'){
            // #d -> #b
            return decToBv(i.substr(2, i.size() - 2));
        }
        else{
            return natToBv(Integer(i), n);
        }
    }
    std::string bvToInt(const std::string& bv){
        assert(bv[0] == '#' && bv[1] == 'b');
        if(bv[2] == '0'){
            Integer res = 0;
            for(size_t i = 3; i < bv.size(); i++){
                res = res * 2 + (bv[i] == '1' ? 1 : 0);
            }
            return res.toString();
        }
        else{
            Integer res = -1;
            for(size_t i = 3; i < bv.size(); i++){
                res = res * 2 + (bv[i] == '0' ? 1 : 0);
            }
            return res.toString();
        }
    }
    std::string intToBv(const Integer& i, const Integer& n){
        if(i >= 0){
            std::string res = "#b0";
            std::string bin = i.toString(2);
            if(bin.size() < n.toULong()){
                res += std::string(n.toULong() - bin.size(), '0') + bin;
            }
            else{
                res += bin.substr(bin.size() - i.toULong(), i.toULong());
            }
            return res;
        }
        else{
            std::string res = "#b1";
            Integer j = -i;
            std::string bin = j.toString(2);
            if(bin.size() < n.toULong()){
                res += std::string(n.toULong() - bin.size(), '0') + bin;
            }
            else{
                res += bin.substr(bin.size() - i.toULong(), i.toULong());
            }
            return res;
        }
    }

    // TODO??
    std::string fpToUbv(const std::string& fp, const Integer& n){
        assert(fp[0] == '#' && fp[1] == 'x');
        std::string res = "";
        bool isNeg = fp[2] == '1';
        if(!isNeg){
            res = fp.substr(3, fp.size() - 3);
        }
        else{
            res = fp.substr(3, fp.size() - 3);
        }
        if(res.size() < n.toULong() - 1){
            res = std::string(n.toULong() - res.size() - 1, '0') + res;
        }
        else{
            res = res.substr(res.size() - n.toULong() + 1, n.toULong() - 1);
        }
        if(isNeg){
            res = "b1" + res;
        }
        else{
            res = "b0" + res;
        }
        return res;
    }
    std::string fpToSbv(const std::string& fp, const Integer& n){
        assert(fp[0] == '#' && fp[1] == 'x');
        std::string res = "";
        bool isNeg = fp[2] == '1';
        if(!isNeg){
            res = fp.substr(3, fp.size() - 3);
        }
        else{
            res = "b1" + fp.substr(3, fp.size() - 3);
        }
        if(res.size() < n.toULong() - 1){
            res = std::string(n.toULong() - res.size() - 1, '0') + res;
        }
        else{
            res = res.substr(res.size() - n.toULong() + 1, n.toULong() - 1);
        }
        if(isNeg){
            res = "b1" + res;
        }
        else{
            res = "b0" + res;
        }
        return res;
    }

    std::string strSubstr(const std::string& s, const Integer& i, const Integer& j){
        return s.substr(i.toULong(), j.toULong() - i.toULong());
    }
    bool strPrefixof(const std::string& s, const std::string& t){
        return s.substr(0, t.size()) == t;
    }
    bool strSuffixof(const std::string& s, const std::string& t){
        return s.substr(s.size() - t.size(), t.size()) == t;
    }
    bool strContains(const std::string& s, const std::string& t){
        return s.find(t) != std::string::npos;
    }
    Integer strIndexof(const std::string& s, const std::string& t, const Integer& i){
        size_t pos = s.find(t, i.toULong());
        return pos == std::string::npos ? -1 : pos;
    }
    std::string strCharAt(const std::string& s, const Integer& i){
        return s.substr(i.toULong(), 1);
    }
    std::string strUpdate(const std::string& s, const Integer& i, const std::string& t){
        return s.substr(0, i.toULong()) + t + s.substr(i.toULong() + t.size(), s.size() - i.toULong() - t.size());
    }
    std::string strReplace(const std::string& s, const std::string& t, const std::string& u){
        size_t pos = s.find(t);
        if(pos == std::string::npos) return s;
        return s.substr(0, pos) + u + s.substr(pos + t.size(), s.size() - pos - t.size());
    }
    std::string strReplaceAll(const std::string& s, const std::string& t, const std::string& u){
        std::string res = s;
        size_t pos = res.find(t);
        while(pos != std::string::npos){
            res = res.substr(0, pos) + u + res.substr(pos + t.size(), res.size() - pos - t.size());
            pos = res.find(t, pos + u.size());
        }
        return res;
    }
    std::string strToLower(const std::string& s){
        std::string res = s;
        for(char& c : res){
            c = tolower(c);
        }
        return res;
    }
    std::string strToUpper(const std::string& s){
        std::string res = s;
        for(char& c : res){
            c = toupper(c);
        }
        return res;
    }
    std::string strRev(const std::string& s){
        return std::string(s.rbegin(), s.rend());
    }


    // toString
    std::string toString(const Integer& i){
        return i.toString();
    }
    std::string toString(const Real& r){
        return r.toString();
    }
    std::string toString(const int& i){
        return std::to_string(i);
    }
    std::string toString(const double& d){
        return std::to_string(d);
    }
    std::string toString(const float& f){
        return std::to_string(f);
    }
    std::string toString(const long& l){
        return std::to_string(l);
    }
    std::string toString(const short& s){
        return std::to_string(s);
    }
    std::string toString(const char& c){
        return std::string(1, c);
    }
    std::string toString(const bool& b){
        return b ? "true" : "false";
    }
}
