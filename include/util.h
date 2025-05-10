/* -*- Header -*-
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
#ifndef UTIL_HEADER
#define UTIL_HEADER

#include "kind.h"

#include <iostream>
#include <iomanip>
#include <sstream>
#include <vector>
#include <cstdint>

namespace SMTLIBParser{

    bool isIntUtil(const std::string& str);
    bool isRealUtil(const std::string& str);
    bool isBVUtil(const std::string& str);
    bool isFPUtil(const std::string& str);
    bool isStrUtil(const std::string& str);
    bool isScientificNotationUtil(const std::string& str);
    std::string parseScientificNotation(const std::string& str);

    Integer pow(const Integer& base, const Integer& exp);
    Integer gcd(const Integer& a, const Integer& b);
    Integer lcm(const Integer& a, const Integer& b);
    Real sqrt(const Integer& i);
    Real sqrt(const Real& r);
    Integer ceil(const Real& r);
    Integer floor(const Real& r);
    Integer round(const Real& r);

    bool isPrime(const Integer& n);
    bool isEven(const Integer& n);
    bool isOdd(const Integer& n);

    Integer factorial(const Integer& n);

    std::string bvToNat(const std::string& bv);
    std::string natToBv(const Integer& i, const Integer& n);
    std::string natToBv(const std::string& i, const Integer& n);
    std::string bvToInt(const std::string& bv);
    std::string intToBv(const Integer& i, const Integer& n);

    std::string bvNot(const std::string& bv);
    std::string bvAnd(const std::string& bv1, const std::string& bv2);
    std::string bvOr(const std::string& bv1, const std::string& bv2);
    std::string bvXor(const std::string& bv1, const std::string& bv2);
    std::string bvNand(const std::string& bv1, const std::string& bv2);
    std::string bvNor(const std::string& bv1, const std::string& bv2);
    std::string bvXnor(const std::string& bv1, const std::string& bv2);

    std::string bvNeg(const std::string& bv);
    std::string bvAdd(const std::string& bv1, const std::string& bv2);
    std::string bvSub(const std::string& bv1, const std::string& bv2);
    std::string bvMul(const std::string& bv1, const std::string& bv2);

    std::string bvUdiv(const std::string& bv1, const std::string& bv2);
    std::string bvUrem(const std::string& bv1, const std::string& bv2);
    std::string bvSdiv(const std::string& bv1, const std::string& bv2);
    std::string bvSrem(const std::string& bv1, const std::string& bv2);
    std::string bvSmod(const std::string& bv1, const std::string& bv2);

    std::string bvShl(const std::string& bv, const std::string& n);
    std::string bvLshr(const std::string& bv, const std::string& n);
    std::string bvAshr(const std::string& bv, const std::string& n);

    std::string bvConcat(const std::string& bv1, const std::string& bv2);
    std::string bvExtract(const std::string& bv, const Integer& i, const Integer& j);
    std::string bvRepeat(const std::string& bv, const Integer& n);
    std::string bvZeroExtend(const std::string& bv, const Integer& n);
    std::string bvSignExtend(const std::string& bv, const Integer& n);

    std::string bvRotateLeft(const std::string& bv, const Integer& n);
    std::string bvRotateRight(const std::string& bv, const Integer& n);

    bool bvComp(const std::string& bv1, const std::string& bv2, const NODE_KIND& kind);

    std::string fpToUbv(const std::string& fp, const Integer& n);
    std::string fpToSbv(const std::string& fp, const Integer& n);

    std::string strSubstr(const std::string& s, const Integer& i, const Integer& j);
    bool        strPrefixof(const std::string& s, const std::string& t);
    bool        strSuffixof(const std::string& s, const std::string& t);
    bool        strContains(const std::string& s, const std::string& t);
    Integer     strIndexof(const std::string& s, const std::string& t, const Integer& i);
    std::string strCharAt(const std::string& s, const Integer& i);
    std::string strUpdate(const std::string& s, const Integer& i, const std::string& t);
    std::string strReplace(const std::string& s, const std::string& t, const std::string& u);
    std::string strReplaceAll(const std::string& s, const std::string& t, const std::string& u);
    std::string strToLower(const std::string& s);
    std::string strToUpper(const std::string& s);
    std::string strRev(const std::string& s);

    std::string toString(const Integer& i);
    std::string toString(const Rational& r);
    std::string toString(const Real& r);

    
    class SHA256 {
    public:
        // Static function to get the SHA256 hash of a string
        static std::string hash(const std::string &input) {
            static SHA256 sha256;  // A static SHA256 object
            sha256.reset();        // Reset the state before using it
            return sha256.process(input);
        }
    
    private:
        uint32_t state[8];  // Hash values
        uint64_t bitLength; // Total bit length of input
    
        // SHA-256 constants (first 32 bits of the fractional parts of the square roots of the first 64 primes)
        static constexpr uint32_t k[64] = {
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0x3192c4fd, 0x2b8e1e4d, 0x7f2a7c67, 0x94f82a4d, 0x37533f4f, 0x5f8a1e10, 0x43172f60,
            0x8e44a3f8, 0x88d7e7ed, 0xd0c8c12d, 0x35da6c31, 0x6e37a0df, 0x6071b9b1, 0xa62e53bc, 0x37b156f3,
            0x8ff8ed2b, 0xa6e472e2, 0xa3c68864, 0x3be12e2e, 0x9d6c71fe, 0x3f775f6b, 0xa852adf7, 0x5b2266a7,
            0xe1be9d35, 0x3da7096d, 0xf8c7032a, 0x2b4b9c0c, 0x438156fd, 0x2d35b6b9, 0x3ff58e3f, 0x94a15ec5,
            0x4d27c0ee, 0x5a15a079, 0x771b6d91, 0x437f394f, 0x69e2a63f, 0x711c312f, 0x5b9d674f, 0x8e88c877
        };
    
        // Constructor, initializing the hash values (state)
        SHA256() {
            reset();
        }
    
        // Reset the state (called before each new hash calculation)
        void reset() {
            // Initial hash values (Constants)
            state[0] = 0x6a09e667;
            state[1] = 0xbb67ae85;
            state[2] = 0x3c6ef372;
            state[3] = 0xa54ff53a;
            state[4] = 0x510e527f;
            state[5] = 0x9b05688c;
            state[6] = 0x1f83d9ab;
            state[7] = 0x5be0cd19;
            
            // Padding length and bit length initialization
            bitLength = 0;
        }
    
        // Function to process the input string and return the hash
        std::string process(const std::string &input) {
            // Handle empty input
            if (input.empty()) {
                // Process a single block with just padding
                std::vector<uint8_t> data(64, 0);
                data[0] = 0x80; // Append 1 bit
                data[63] = 0;   // Message length is 0
                processBlock(data.data());
                return toHexString();
            }

            // Step 1: Padding the input
            std::vector<uint8_t> data = padInput(input);
    
            // Step 2: Processing each 512-bit block
            for (size_t i = 0; i < data.size(); i += 64) {
                processBlock(&data[i]);
            }
    
            // Step 3: Output the final hash
            return toHexString();
        }
    
        // Padding the input according to the SHA-256 specification
        std::vector<uint8_t> padInput(const std::string &input) {
            std::vector<uint8_t> data(input.begin(), input.end());
            bitLength = input.size() * 8;
            
            // Append a 1 bit (0x80) to the input
            data.push_back(0x80);
    
            // Append 0 bits until the length is congruent to 448 mod 512
            while ((data.size() * 8) % 512 != 448) {
                data.push_back(0x00);
            }
    
            // Append the length of the original message (in bits) as a 64-bit big-endian integer
            for (int i = 7; i >= 0; --i) {
                data.push_back(static_cast<uint8_t>((bitLength >> (i * 8)) & 0xFF));
            }
    
            return data;
        }
    
        // Process a 512-bit block of data (64 bytes)
        void processBlock(const uint8_t *block) {
            uint32_t w[64];
            
            // Break the block into 16 32-bit words
            for (int i = 0; i < 16; i++) {
                w[i] = (block[i * 4] << 24) |
                       (block[i * 4 + 1] << 16) |
                       (block[i * 4 + 2] << 8) |
                       (block[i * 4 + 3]);
            }
    
            // Extend the 16 words into 64 words
            for (int i = 16; i < 64; i++) {
                uint32_t s0 = rightRotate(w[i - 15], 7) ^ rightRotate(w[i - 15], 18) ^ (w[i - 15] >> 3);
                uint32_t s1 = rightRotate(w[i - 2], 17) ^ rightRotate(w[i - 2], 19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16] + s0 + w[i - 7] + s1;
            }
    
            // Initialize the working variables with the current hash values
            uint32_t a = state[0];
            uint32_t b = state[1];
            uint32_t c = state[2];
            uint32_t d = state[3];
            uint32_t e = state[4];
            uint32_t f = state[5];
            uint32_t g = state[6];
            uint32_t h = state[7];
    
            // Main loop
            for (int i = 0; i < 64; i++) {
                uint32_t s1 = rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25);
                uint32_t ch = (e & f) ^ (~e & g);
                uint32_t temp1 = h + s1 + ch + k[i] + w[i];
                uint32_t s0 = rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22);
                uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
                uint32_t temp2 = s0 + maj;
    
                h = g;
                g = f;
                f = e;
                e = d + temp1;
                d = c;
                c = b;
                b = a;
                a = temp1 + temp2;
            }
    
            // Add the working variables to the current hash values
            state[0] += a;
            state[1] += b;
            state[2] += c;
            state[3] += d;
            state[4] += e;
            state[5] += f;
            state[6] += g;
            state[7] += h;
        }
    
        // Convert the final state (hash) to a hexadecimal string
        std::string toHexString() {
            std::stringstream ss;
            for (int i = 0; i < 8; i++) {
                ss << std::setw(8) << std::setfill('0') << std::hex << state[i];
            }
            return ss.str();
        }
    
        // Right rotate a 32-bit word
        uint32_t rightRotate(uint32_t value, uint32_t count) {
            return (value >> count) | (value << (32 - count));
        }
    };

    std::string sha256(const std::string& input);
}

#endif
