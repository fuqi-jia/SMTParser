/* -*- Header -*-
 *
 * The Option Class
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
#ifndef _OPTIONS_H
#define _OPTIONS_H

#include "asserting.h"
#include <unordered_map>

namespace SMTParser{
    class GlobalOptions {
    public:
        // ENUM_LOGIC logic = UNKNOWN_LOGIC;
        std::string logic = "UNKNOWN_LOGIC";
        bool check_sat = false;
        bool get_assertions = false;
        bool get_assignment = false;
        // set-info
        std::unordered_map<std::string, std::string> info;
        // get-info
        std::unordered_map<std::string, std::string> get_info;
        bool get_model = false;
        // set-option
        std::unordered_map<std::string, std::string> options;
        // get-option
        std::unordered_map<std::string, std::string> get_options;
        bool get_proof = false;
        bool get_unsat_assumptions = false;
        bool get_unsat_core = false;
        // get-value
        std::unordered_map<std::string, std::string> values;

        // get-objectives
        bool get_objectives = false;

        // evaluate precision
        bool evaluate_use_floating = true;
        mpfr_prec_t evaluate_precision = 128;

    public:
        GlobalOptions() = default;
        ~GlobalOptions() = default;

        bool setLogic(const std::string& logic_name) {
            if( logic_name == "QF_ABV" || 
                logic_name == "QF_ABVFP" ||
                logic_name == "QF_ABVFPLRA" ||
                logic_name == "QF_ALIA" ||
                logic_name == "QF_ANIA" ||
                logic_name == "QF_AUFBV" ||
                logic_name == "QF_AUFBVFP" ||
                logic_name == "QF_AUFLIA" ||
                logic_name == "QF_AUFNIA" ||
                logic_name == "QF_AX" ||
                logic_name == "QF_BV" ||
                logic_name == "QF_BVFP" ||
                logic_name == "QF_DT" ||
                logic_name == "QF_BVFPLRA" ||
                logic_name == "QF_FP" ||
                logic_name == "QF_FPLRA" ||
                logic_name == "QF_IDL" ||
                logic_name == "QF_LIA" ||
                logic_name == "QF_LIRA" ||
                logic_name == "QF_LRA" ||
                logic_name == "QF_NIA" ||
                logic_name == "QF_NIRA" ||
                logic_name == "QF_NRA" ||
                logic_name == "QF_RDL" ||
                logic_name == "QF_S" ||
                logic_name == "QF_SLIA" ||
                logic_name == "QF_SNIA" ||
                logic_name == "QF_UF" ||
                logic_name == "QF_UFBV" ||
                logic_name == "QF_UFBVDT" ||
                logic_name == "QF_UFDT" ||
                logic_name == "QF_UFDTLIA" ||
                logic_name == "QF_UFDTLIRA" ||
                logic_name == "QF_UFDTNIA" ||
                logic_name == "QF_UFFP" ||
                logic_name == "QF_UFFPDTNIRA" ||
                logic_name == "QF_UFIDL" ||
                logic_name == "QF_UFLIA" ||
                logic_name == "QF_UFLRA" ||
                logic_name == "QF_UFNIA" ||
                logic_name == "QF_UFNRA" ||
                logic_name == "AUFLIA" ||
                logic_name == "AUFLIRA" ||
                logic_name == "AUFNIRA" ||
                logic_name == "LIA" ||
                logic_name == "LRA" ||
                logic_name == "UFLRA" ||
                logic_name == "UFNIA" ||
                logic_name == "ALL") {
                    logic = logic_name;
                    return true;
                } else {
                    logic = "UNKNOWN_LOGIC";
                    return false;
                }
        }

        void setOption(const std::string& key, const std::string& value) {
            options[key] = value;
        }

        void setInfo(const std::string& key, const std::string& value) {
            info[key] = value;
        }

        std::string getLogic() const {
            return logic;
        }

        void getValue(const std::string& key, const std::string& value) {
            values[key] = value;
        }

        void getInfo(const std::string& key, const std::string& value) {
            get_info[key] = value;
        }

        void getOption(const std::string& key, const std::string& value) {
            get_options[key] = value;
        }

        
        // logic checking
        bool isIntTheory() const {
            return logic.find("I") != std::string::npos && logic.find("R") == std::string::npos;
        }
        bool isRealTheory() const {
            return logic.find("R") != std::string::npos;
        }
        bool isIntRealTheory() const {
            return logic.find("I") != std::string::npos && logic.find("R") != std::string::npos;
        }

        void setEvaluatePrecision(mpfr_prec_t precision) {
            evaluate_precision = precision;
        }

        mpfr_prec_t getEvaluatePrecision() const {
            return evaluate_precision;
        }

        void setEvaluateUseFloating(bool use_floating) {
            evaluate_use_floating = use_floating;
        }

        bool getEvaluateUseFloating() const {
            return evaluate_use_floating;
        }
        
    };
}
#endif // _OPTIONS_H