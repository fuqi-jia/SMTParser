/* -*- Header -*-
 *
 * The Numbers
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

#ifndef NUMBER_HEADER
#define NUMBER_HEADER

#include <gmp.h>
#include <gmpxx.h>
#include <mpfr.h>
#include <string>

namespace SMTLIBParser{
    typedef mpz_class Integer;
    // typedef mpf_class Real;
    
    class HighPrecisionReal{
        public:
            // 常量
            static HighPrecisionReal pi(mpfr_prec_t precision = 128);  // π (pi)
            static HighPrecisionReal e(mpfr_prec_t precision = 128);   // e (natural logarithm base)
            static HighPrecisionReal phi(mpfr_prec_t precision = 128); // φ (golden ratio)
            static HighPrecisionReal ln2(mpfr_prec_t precision = 128); // ln(2)
            static HighPrecisionReal ln10(mpfr_prec_t precision = 128); // ln(10)
            static HighPrecisionReal log2_e(mpfr_prec_t precision = 128); // log₂(e)
            static HighPrecisionReal log10_e(mpfr_prec_t precision = 128); // log₁₀(e)
            static HighPrecisionReal euler(mpfr_prec_t precision = 128); // γ (Euler constant)
            static HighPrecisionReal catalan(mpfr_prec_t precision = 128); // G (Catalan constant)
            
            // Constructor
            HighPrecisionReal(mpfr_prec_t precision = 128);
            HighPrecisionReal(int i, mpfr_prec_t precision = 128);
            // HighPrecisionReal(const Real& r, mpfr_prec_t precision = 128);
            HighPrecisionReal(const Integer& i, mpfr_prec_t precision = 128);
            HighPrecisionReal(const double& d, mpfr_prec_t precision = 128);
            HighPrecisionReal(const float& f, mpfr_prec_t precision = 128);
            HighPrecisionReal(const std::string& s, mpfr_prec_t precision = 128);
            HighPrecisionReal(const char* s, mpfr_prec_t precision = 128);
            HighPrecisionReal(const HighPrecisionReal& other);
            
            // Assignment operator
            HighPrecisionReal& operator=(const HighPrecisionReal& other);
            
            // Destructor
            ~HighPrecisionReal();
            
            // Basic arithmetic operators
            HighPrecisionReal operator+(const HighPrecisionReal& other) const;
            HighPrecisionReal operator-(const HighPrecisionReal& other) const;
            HighPrecisionReal operator-() const;
            HighPrecisionReal operator*(const HighPrecisionReal& other) const;
            HighPrecisionReal operator/(const HighPrecisionReal& other) const;
            HighPrecisionReal& operator+=(const HighPrecisionReal& other);
            HighPrecisionReal& operator-=(const HighPrecisionReal& other);
            HighPrecisionReal& operator*=(const HighPrecisionReal& other);
            HighPrecisionReal& operator/=(const HighPrecisionReal& other);
            
            // Comparison operators
            bool operator==(const HighPrecisionReal& other) const;
            bool operator!=(const HighPrecisionReal& other) const;
            bool operator<(const HighPrecisionReal& other) const;
            bool operator<=(const HighPrecisionReal& other) const;
            bool operator>(const HighPrecisionReal& other) const;
            bool operator>=(const HighPrecisionReal& other) const;
            
            // Other operations
            HighPrecisionReal abs() const;
            HighPrecisionReal sqrt() const;
            HighPrecisionReal safeSqrt() const;
            HighPrecisionReal pow(const HighPrecisionReal& exp) const;
            
            // Rounding operations
            HighPrecisionReal ceil() const;
            HighPrecisionReal floor() const;
            HighPrecisionReal round() const;
            
            // Exponential and logarithmic functions
            HighPrecisionReal exp() const;
            HighPrecisionReal ln() const;
            HighPrecisionReal lg() const;
            HighPrecisionReal lb() const;
            HighPrecisionReal log(const HighPrecisionReal& base) const;
            
            // Trigonometric functions
            HighPrecisionReal sin() const;
            HighPrecisionReal cos() const;
            HighPrecisionReal tan() const;
            HighPrecisionReal asin() const;
            HighPrecisionReal acos() const;
            HighPrecisionReal atan() const;
            static HighPrecisionReal atan2(const HighPrecisionReal& y, const HighPrecisionReal& x);
            
            // Hyperbolic functions
            HighPrecisionReal sinh() const;
            HighPrecisionReal cosh() const;
            HighPrecisionReal tanh() const;
            HighPrecisionReal asinh() const;
            HighPrecisionReal acosh() const;
            HighPrecisionReal atanh() const;
            HighPrecisionReal asech() const;
            HighPrecisionReal acsch() const;
            HighPrecisionReal acoth() const;
            
            // Conversion functions
            std::string toString() const;
            double toDouble() const;
            float toFloat() const;
            int toInt() const;
            long long toLongLong() const;
            Integer toInteger() const;
            // Set and get precision
            void setPrecision(mpfr_prec_t precision);
            mpfr_prec_t getPrecision() const;
            
            // Access internal MPFR value
            mpfr_ptr getMPFR();
            mpfr_srcptr getMPFR() const;
            
        private:
            mpfr_t value;
    };

    typedef HighPrecisionReal Real;
}

#endif

