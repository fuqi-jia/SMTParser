/* -*- Source -*-
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

#include "number.h"
#include <stdexcept>
#include <cstring>
#include <cmath>

namespace SMTLIBParser {

// 常量
HighPrecisionReal HighPrecisionReal::pi(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_pi(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // use exp(1) to calculate e
    mpfr_set_ui(result.value, 1, MPFR_RNDN);
    mpfr_exp(result.value, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::phi(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // φ = (1 + sqrt(5)) / 2
    HighPrecisionReal five(5, precision);
    HighPrecisionReal sqrt5 = five.sqrt();
    HighPrecisionReal one(1, precision);
    mpfr_add(result.value, one.value, sqrt5.value, MPFR_RNDN);
    mpfr_div_ui(result.value, result.value, 2, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln2(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_log2(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln10(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    HighPrecisionReal ten(10, precision);
    mpfr_log(result.value, ten.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log2_e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // log₂(e) = 1/ln(2)
    mpfr_const_log2(result.value, MPFR_RNDN);
    mpfr_ui_div(result.value, 1, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log10_e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // log₁₀(e) = 1/ln(10)
    HighPrecisionReal ten(10, precision);
    mpfr_log(result.value, ten.value, MPFR_RNDN);
    mpfr_ui_div(result.value, 1, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::euler(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_euler(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::catalan(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_catalan(result.value, MPFR_RNDN);
    return result;
}

// Constructor
HighPrecisionReal::HighPrecisionReal(mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_zero(value, 1); // Initialize to +0
}

HighPrecisionReal::HighPrecisionReal(int i, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_si(value, i, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const Real& r, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_f(value, r.get_mpf_t(), MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const Integer& i, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_z(value, i.get_mpz_t(), MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const double& d, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_d(value, d, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const float& f, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_flt(value, f, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const std::string& s, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    if (mpfr_set_str(value, s.c_str(), 10, MPFR_RNDN) != 0) {
        mpfr_clear(value);
        throw std::invalid_argument("Cannot convert string to high precision real number");
    }
}

HighPrecisionReal::HighPrecisionReal(const char* s, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    if (mpfr_set_str(value, s, 10, MPFR_RNDN) != 0) {
        mpfr_clear(value);
        throw std::invalid_argument("Cannot convert string to high precision real number");
    }
}

HighPrecisionReal::HighPrecisionReal(const HighPrecisionReal& other) {
    mpfr_init2(value, mpfr_get_prec(other.value));
    mpfr_set(value, other.value, MPFR_RNDN);
}

// Assignment operator
HighPrecisionReal& HighPrecisionReal::operator=(const HighPrecisionReal& other) {
    if (this != &other) {
        // If precision is different, reinitialize
        if (mpfr_get_prec(value) != mpfr_get_prec(other.value)) {
            mpfr_clear(value);
            mpfr_init2(value, mpfr_get_prec(other.value));
        }
        mpfr_set(value, other.value, MPFR_RNDN);
    }
    return *this;
}

// Destructor
HighPrecisionReal::~HighPrecisionReal() {
    mpfr_clear(value);
}

// Basic arithmetic operators
HighPrecisionReal HighPrecisionReal::operator+(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_add(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator-(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_sub(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator*(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_mul(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator/(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_div(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal& HighPrecisionReal::operator+=(const HighPrecisionReal& other) {
    mpfr_add(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator-=(const HighPrecisionReal& other) {
    mpfr_sub(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator*=(const HighPrecisionReal& other) {
    mpfr_mul(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator/=(const HighPrecisionReal& other) {
    mpfr_div(value, value, other.value, MPFR_RNDN);
    return *this;
}

// Comparison operators
bool HighPrecisionReal::operator==(const HighPrecisionReal& other) const {
    return mpfr_equal_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator!=(const HighPrecisionReal& other) const {
    return !(*this == other);
}

bool HighPrecisionReal::operator<(const HighPrecisionReal& other) const {
    return mpfr_less_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator<=(const HighPrecisionReal& other) const {
    return mpfr_lessequal_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator>(const HighPrecisionReal& other) const {
    return mpfr_greater_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator>=(const HighPrecisionReal& other) const {
    return mpfr_greaterequal_p(value, other.value) != 0;
}

// Other operations
HighPrecisionReal HighPrecisionReal::abs() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_abs(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::sqrt() const {
    if (*this < HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute square root of a negative number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sqrt(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::safeSqrt() const {
    if (*this < HighPrecisionReal(0)) {
        return HighPrecisionReal(0);
    }
    return sqrt();
}

HighPrecisionReal HighPrecisionReal::pow(const HighPrecisionReal& exp) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(exp.value)));
    mpfr_pow(result.value, value, exp.value, MPFR_RNDN);
    return result;
}

// Rounding operations
HighPrecisionReal HighPrecisionReal::ceil() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_ceil(result.value, value);
    return result;
}

HighPrecisionReal HighPrecisionReal::floor() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_floor(result.value, value);
    return result;
}

HighPrecisionReal HighPrecisionReal::round() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_round(result.value, value);
    return result;
}

// Exponential and logarithmic functions
HighPrecisionReal HighPrecisionReal::exp() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_exp(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::lg() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log10(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::lb() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log2(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log(const HighPrecisionReal& base) const {
    if (*this <= HighPrecisionReal(0) || base <= HighPrecisionReal(0) || base == HighPrecisionReal(1)) {
        throw std::domain_error("Invalid arguments for logarithm");
    }
    HighPrecisionReal result = ln();
    HighPrecisionReal baseLog = base.ln();
    mpfr_div(result.value, result.value, baseLog.value, MPFR_RNDN);
    return result;
}

// Trigonometric functions
HighPrecisionReal HighPrecisionReal::sin() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sin(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::cos() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_cos(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::tan() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_tan(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asin() const {
    if (*this < HighPrecisionReal(-1) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for asin must be in range [-1, 1]");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_asin(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acos() const {
    if (*this < HighPrecisionReal(-1) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acos must be in range [-1, 1]");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_acos(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::atan() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_atan(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::atan2(const HighPrecisionReal& y, const HighPrecisionReal& x) {
    mpfr_prec_t precision = std::max(mpfr_get_prec(y.value), mpfr_get_prec(x.value));
    HighPrecisionReal result(precision);
    mpfr_atan2(result.value, y.value, x.value, MPFR_RNDN);
    return result;
}

// Hyperbolic functions
HighPrecisionReal HighPrecisionReal::sinh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sinh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::cosh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_cosh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::tanh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_tanh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asinh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_asinh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acosh() const {
    if (*this < HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acosh must be >= 1");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_acosh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::atanh() const {
    if (*this <= HighPrecisionReal(-1) || *this >= HighPrecisionReal(1)) {
        throw std::domain_error("Argument for atanh must be in range (-1, 1)");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_atanh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asech() const {
    if (*this <= HighPrecisionReal(0) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for asech must be in range (0, 1]");
    }
    // asech(x) = acosh(1/x)
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.acosh();
}

HighPrecisionReal HighPrecisionReal::acsch() const {
    if (*this == HighPrecisionReal(0)) {
        throw std::domain_error("Argument for acsch cannot be 0");
    }
    // acsch(x) = asinh(1/x)
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.asinh();
}

HighPrecisionReal HighPrecisionReal::acoth() const {
    if (*this <= HighPrecisionReal(-1) && *this >= HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acoth must be outside range [-1, 1]");
    }
    // acoth(x) = atanh(1/x)
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.atanh();
}

// Conversion functions
std::string HighPrecisionReal::toString() const {
    mp_exp_t exponent;
    char* str = mpfr_get_str(nullptr, &exponent, 10, 0, value, MPFR_RNDN);
    std::string result;
    
    // Handle sign
    if (str[0] == '-') {
        result = "-";
        memmove(str, str + 1, strlen(str));
    }
    
    // Format number representation
    if (exponent <= 0) {
        result += "0.";
        for (int i = 0; i < -exponent; i++) {
            result += "0";
        }
        result += str;
    } else if (exponent < static_cast<mp_exp_t>(strlen(str))) {
        result.append(str, exponent);
        result += ".";
        result.append(str + exponent);
    } else {
        result += str;
        for (mp_exp_t i = strlen(str); i < exponent; i++) {
            result += "0";
        }
    }
    
    mpfr_free_str(str);
    return result;
}

double HighPrecisionReal::toDouble() const {
    return mpfr_get_d(value, MPFR_RNDN);
}

// Set and get precision
void HighPrecisionReal::setPrecision(mpfr_prec_t precision) {
    mpfr_prec_round(value, precision, MPFR_RNDN);
}

mpfr_prec_t HighPrecisionReal::getPrecision() const {
    return mpfr_get_prec(value);
}

// Access internal MPFR value
mpfr_ptr HighPrecisionReal::getMPFR() {
    return value;
}

mpfr_srcptr HighPrecisionReal::getMPFR() const {
    return value;
}

} // namespace SMTLIBParser 