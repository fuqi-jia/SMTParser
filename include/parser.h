/* -*- Header -*-
 *
 * An SMT/OMT Parser
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

#ifndef PARSER_HEADER
#define PARSER_HEADER

#include "dag.h"
#include "util.h"
#include "options.h"
#include "objective.h"
#include "model.h"

#include <boost/unordered_set.hpp>



namespace SMTLIBParser{
    enum class SCAN_MODE {
        SM_COMMON,
        SM_SYMBOL,
        SM_COMP_SYM,
        SM_COMMENT,
        SM_STRING
    };

    enum class KEYWORD{
        KW_ID, KW_WEIGHT, KW_COMP, KW_EPSILON, KW_M, KW_OPT_KIND, KW_NULL
    };

    enum class CMD_TYPE {
        CT_UNKNOWN, CT_EOF,
        // COMMANDS
        CT_ASSERT, CT_CHECK_SAT, CT_CHECK_SAT_ASSUMING,
        CT_DECLARE_CONST, CT_DECLARE_FUN, CT_DECLARE_SORT,
        CT_DEFINE_FUN, CT_DEFINE_FUN_REC, CT_DEFINE_FUNS_REC, CT_DEFINE_SORT,
        CT_ECHO, CT_EXIT,
        CT_GET_ASSERTIONS, CT_GET_ASSIGNMENT, CT_GET_INFO,
        CT_GET_MODEL, CT_GET_OPTION, CT_GET_PROOF,
        CT_GET_UNSAT_ASSUMPTIONS, CT_GET_UNSAT_CORE, CT_GET_VALUE,
        CT_POP, CT_PUSH, CT_RESET, CT_RESET_ASSERTIONS,
        CT_SET_INFO, CT_SET_LOGIC, CT_SET_OPTION,
        // QUANTIFIER
        CT_EXISTS, CT_FORALL,
        // OPTIMIZATION COMMANDS
        CT_GET_OBJECTIVES, CT_ASSERT_SOFT, 
        CT_DEFINE_OBJ, CT_DEFINE_MIN_OBJ, CT_DEFINE_MAX_OBJ,
        CT_MINIMIZE, CT_MAXIMIZE, CT_LEX_OPTIMIZE, CT_PARETO_OPTIMIZE, CT_BOX_OPTIMIZE, CT_MINMAX, CT_MAXMIN, CT_MAXSAT, CT_MINSAT, CT_OPTIMIZE
        // CT_LEX_MAXIMIZE, CT_PARETO_MINIMIZE, CT_PARETO_MAXIMIZE, 
        // CT_BOX_MINIMIZE, CT_BOX_MAXIMIZE, CT_MINMAX, CT_MAXMIN
    };

    enum class ERROR_TYPE {
        ERR_UNEXP_EOF,
        ERR_SYM_MIS,
        ERR_UNKWN_SYM,
        ERR_PARAM_MIS,
        ERR_PARAM_NBOOL,
        ERR_PARAM_NNUM,
        ERR_PARAM_NSAME,
        ERR_LOGIC,
        ERR_MUL_DECL,
        ERR_MUL_DEF,
        ERR_ZERO_DIVISOR,
        ERR_FUN_LOCAL_VAR,
        ERR_ARI_MIS,
        ERR_TYPE_MIS,
        ERR_NEG_PARAM
    };


    /*
    Parser
    */

    // NOTE: only non-incremental mode
    class Parser {
    private:

        // attributes

        // vars for parser
        char 			                        *buffer;
        unsigned long	                        buflen;
        char			                        *bufptr;
        size_t 	                                line_number;
        SCAN_MODE 		                        scan_mode;

        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                let_key_map; // local variables, no need to hash store
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                fun_key_map; 
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>> 
                                                fun_var_map; // variables are not the same, no need to hash store
        boost::unordered_map<std::string, std::shared_ptr<Sort>>
                                                sort_key_map;
        boost::unordered_map<std::string, std::shared_ptr<DAGNode>>
                                                quant_var_map;
        std::vector<std::shared_ptr<DAGNode>>   static_functions; // static functions without substitution

        // FOL binding

        // node list
        std::vector<std::shared_ptr<DAGNode>>           node_list;
        // variable name list
        boost::unordered_map<std::string, size_t>       var_names;
        // const node
        boost::unordered_map<std::string, size_t>       constants;
        // temp var name list
        size_t temp_var_counter;
        boost::unordered_map<std::string, size_t>       temp_var_names;
        // function name list
        std::vector<std::string>                        function_names;
        // global options
        std::shared_ptr<GlobalOptions>                  options;
        // hash value list
        boost::unordered_map<std::shared_ptr<DAGNode>, size_t, NodeHash, NodeEqual>
                                                        complex_node_map;
        // (define-objective name single_opt)
        boost::unordered_map<std::string, std::shared_ptr<Objective>> 
                                                        objective_map;
        // conversion map
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        cnf_map;
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        dnf_map;
        boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        nnf_map;

    public:
        std::vector<std::shared_ptr<DAGNode>>               assertions;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> 
                                                            assertion_groups;
        std::vector<std::vector<std::shared_ptr<DAGNode>>>  assumptions;
        std::vector<std::shared_ptr<DAGNode>>               soft_assertions;
        std::vector<std::shared_ptr<DAGNode>>               soft_weights;
        boost::unordered_map<std::string, boost::unordered_set<size_t>> 
                                                            soft_assertion_groups;
        std::vector<std::shared_ptr<Objective>>             objectives;


    public:
        
        /**
         * @brief Constructor with filename
         * 
         * Creates a Parser object and immediately tries to parse the specified SMT-LIB2 file.
         * 
         * @param filename Path to the SMT-LIB2 file to parse
         */
        Parser(const std::string& filename);
        
        /**
         * @brief Default constructor
         * 
         * Creates an empty Parser object, parse method must be called later to parse a file.
         */
        Parser();
        
        /**
         * @brief Destructor
         * 
         * Releases all resources used by the Parser
         */
        ~Parser();
        
        /**
         * @brief Parse SMT-LIB2 file
         * 
         * Parses the specified SMT-LIB2 file and builds internal data structures.
         * 
         * @param filename Path to the SMT-LIB2 file to parse
         * @return True if parsing was successful, false otherwise
         */
        bool parse(const std::string& filename);

        // to solver
        /**
         * @brief Get all assertions
         * 
         * Returns a vector of all assertions.
         * 
         * @return Vector of all assertions
         */
        std::vector<std::shared_ptr<DAGNode>> getAssertions() const;

        /**
         * @brief Get grouped assertions
         *
         * Returns assertion groups map. Use (assert expr :id group_name) to assign 
         * assertions to groups. Assertions without an ID go to the default group.
         *
         * @return Map from group names to sets of assertion indices
         */
        boost::unordered_map<std::string, boost::unordered_set<size_t>> getGroupedAssertions() const;

        /**
         * @brief Get assumptions
         * 
         * Returns a vector of all assumptions. Use (check-sat-assuming (assumptions)) to check satisfiability
         * under the given assumptions.
         * 
         * @return Vector of all assumptions
         */ 
        std::vector<std::vector<std::shared_ptr<DAGNode>>> getAssumptions() const;

        /**
         * @brief Get soft assertions
         * 
         * Returns soft assertions. Use (assert-soft expr :weight weight :id group_name) to group and weight them.
         * 
         * @return Vector of all soft assertions
         */
        std::vector<std::shared_ptr<DAGNode>> getSoftAssertions() const;

        /**
         * @brief Get soft assertion weights
         * 
         * Returns a vector of all soft assertion weights.
         * 
         * @return Vector of all soft assertion weights
         */
        std::vector<std::shared_ptr<DAGNode>> getSoftWeights() const;

        /**
         * @brief Get grouped soft assertions
         * 
         * Returns a map of soft assertion groups. Use (assert-soft expr :weight weight :id group_name) to group and weight them.
         * 
         * @return Map from group names to sets of soft assertion indices
         */
        boost::unordered_map<std::string, boost::unordered_set<size_t>> getGroupedSoftAssertions() const;

        /**
         * @brief Get objectives
         * 
         * Returns a vector of all objectives.
         * 
         * @return Vector of all objectives
         */
        std::vector<std::shared_ptr<Objective>> getObjectives() const;

        /**
         * @brief Get global options
         * 
         * Returns a pointer to the global options.
         * 
         * @return Pointer to global options
         */
        std::shared_ptr<GlobalOptions> getOptions() const;

        /**
         * @brief Get variables
         * 
         * Returns a vector of all variables.
         * 
         * @return Vector of all variables
         */
        std::vector<std::shared_ptr<DAGNode>> getVariables() const;

        /**
         * @brief Get functions
         * 
         * Returns a vector of all functions. Use (define-fun name (params) body) to define a function.
         * 
         * @return Vector of all functions
         */
        std::vector<std::shared_ptr<DAGNode>> getFunctions() const;

        // get sort
        /**
         * @brief Get sort
         * 
         * Returns a sort for the given parameters.
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(const std::vector<std::shared_ptr<DAGNode>>& params);

        /**
         * @brief Get sort
         * 
         * Returns a sort for the given parameter.
         * 
         * @param param Parameter
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> param);

        /**
         * @brief Get sort
         * 
         * Returns a sort for the given parameters.
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Get sort
         * 
         * Returns a sort for the given parameters.
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> m);

        // mk oper 
        /**
         * @brief Create an operation
         * 
         * Creates an operation with the given sort and parameters.
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param p Parameters
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p);

        /**
         * @brief Create an operation
         * 
         * Creates an operation with the given sort and parameters.
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param l Left parameter
         * @param r Right parameter
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create an operation
         * 
         * Creates an operation with the given sort and parameters.
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Operation Node
         */     
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create an operation
         * 
         * Creates an operation with the given sort and parameters.
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param p Parameters
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p);

        /**
         * @brief Simplify an operation
         * 
         * Simplifies an operation with the given kind and parameters.
         * 
         * @note The parameters are assumed to be constant.
         * 
         * @param t Operation kind
         * @param p Parameters
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> p);

        /**
         * @brief Simplify an operation
         * 
         * Simplifies an operation with the given kind and parameters.
         * 
         * @note The parameters are assumed to be constant.
         * 
         * @param t Operation kind
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Simplify an operation
         * 
         * Simplifies an operation with the given kind and parameters.
         * 
         * @param t Operation kind
         * @param p Parameters
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p);

        // mk function
        /**
         * @brief Create a function declaration
         * 
         * Creates a function declaration with the given name, parameters, and output sort.
         * 
         * @param name Function name
         * @param params Parameters
         * @param out_sort Output sort
         * @return Function declaration node
         */
        std::shared_ptr<DAGNode> mkFuncDec(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);

        /**
         * @brief Create a function definition
         * 
         * Creates a function definition with the given name, parameters, output sort, and body.
         * 
         * @param name Function name
         * @param params Parameters
         * @param out_sort Output sort
         * @param body Body
         * @return Function definition node
         */
        std::shared_ptr<DAGNode> mkFuncDef(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body);

        // mk sort
        /**
         * @brief Create a sort declaration
         * 
         * Creates a sort declaration with the given name and arity.
         * 
         * @param name Sort name
         * @param arity Arity
         * @return Sort declaration node
         */
        std::shared_ptr<Sort> mkSortDec(const std::string &name, const size_t &arity);
        // mk true/false
        /**
         * @brief Create a true node
         * 
         * Creates a true node.
         * 
         * @return True node
         */
        std::shared_ptr<DAGNode>	mkTrue(); // true

        /**
         * @brief Create a false node
         * 
         * Creates a false node.
         * 
         * @return False node
         */
        std::shared_ptr<DAGNode>	mkFalse(); // false

        /**
         * @brief Create an unknown node
         * 
         * Creates an unknown node.
         * 
         * @return Unknown node
         */
        std::shared_ptr<DAGNode>    mkUnknown(); // unknown
        // CORE OPERATORS
        /**
         * @brief Create an equality node
         * 
         * Creates an equality node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Equality node
         */
        std::shared_ptr<DAGNode> mkEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r

        /**
         * @brief Create an equality node
         * 
         * Creates an equality node with the given parameters.
         * 
         * @param params Parameters
         * @return Equality node
         */
        std::shared_ptr<DAGNode> mkEq(const std::vector<std::shared_ptr<DAGNode>>& params); // l = r = ... 
        
        /**
         * @brief Create a distinct node
         * 
         * Creates a distinct node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Distinct node
         */
        std::shared_ptr<DAGNode> mkDistinct(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create a distinct node
         * 
         * Creates a distinct node with the given parameters.
         * 
         * @param params Parameters
         * @return Distinct node
         */
        std::shared_ptr<DAGNode> mkDistinct(const std::vector<std::shared_ptr<DAGNode>> &params); // l != r != ...
        
        // CONST
        /**
         * @brief Create a constant node
         * 
         * Creates a constant node with the given sort and value.
         * 
         * @param sort Sort
         * @param v Value (string)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const std::string &v); // CONST

        
        /**
         * @brief Create an integer constant
         *
         * Creates a constant node with the given sort and integer value.
         *
         * @param sort Sort
         * @param v Value (int)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const int& v); // CONST_INT

        /**
         * @brief Create a real constant from double
         *
         * Creates a constant node with the given sort and double value.
         *
         * @param sort Sort
         * @param v Value (double)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const double& v); // CONST_REAL

        /**
         * @brief Create a real constant
         *
         * Creates a constant node with the given sort and high-precision real value.
         *
         * @param sort Sort
         * @param v Value (double)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const Real& v); // CONST_REAL

        /**
         * @brief Create a numeric constant
         *
         * Creates a constant node with the given sort and arbitrary-precision integer value.
         *
         * @param sort Sort
         * @param v Value (Integer)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const Integer& v); // CONST_REAL/INT

        /**
         * @brief Create a boolean constant
         *
         * Creates a constant node with the given sort and boolean value.
         *
         * @param sort Sort
         * @param v Value (bool)
         * @return Constant node
         */
        std::shared_ptr<DAGNode> mkConst(const std::shared_ptr<Sort>& sort, const bool& v); // CONST_BOOL
        
        /**
         * @brief Create a boolean constant
         *
         * Creates a boolean constant node with the given boolean value.
         *
         * @param v Value (bool)
         * @return Boolean constant node
         */
        std::shared_ptr<DAGNode> mkConstBool(const bool &v); // CONST_BOOL
        
        /**
         * @brief Create a boolean constant from integer
         *
         * Creates a boolean constant node from an integer value (0 = false, non-0 = true).
         *
         * @param v Value (int)
         * @return Boolean constant node
         */
        std::shared_ptr<DAGNode> mkConstBool(const int& v); // CONST_BOOL
        
        /**
         * @brief Create a boolean constant from string
         *
         * Creates a boolean constant node from a string ("true"/"false").
         *
         * @param v Value (string)
         * @return Boolean constant node
         */
        std::shared_ptr<DAGNode> mkConstBool(const std::string &v); // CONST_BOOL
        
        /**
         * @brief Create a boolean constant from double
         *
         * Creates a boolean constant node from a double value (0.0 = false, non-0 = true).
         *
         * @param v Value (double)
         * @return Boolean constant node
         */
        std::shared_ptr<DAGNode> mkConstBool(const double &v); // CONST_BOOL
        
        /**
         * @brief Create an integer constant from string
         *
         * Creates an integer constant node from a string representation.
         *
         * @param v Value (string)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const std::string &v); // CONST_INT
        
        /**
         * @brief Create an integer constant
         *
         * Creates an integer constant node from an integer value.
         *
         * @param v Value (int)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const int& v); // CONST_INT
        
        /**
         * @brief Create an integer constant
         *
         * Creates an integer constant node from an arbitrary-precision integer value.
         *
         * @param v Value (Integer)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const Integer &v); // CONST_INT
        
        /**
         * @brief Create a real constant from string
         *
         * Creates a real constant node from a string representation.
         *
         * @param v Value (string)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const std::string &v); // CONST_REAL
        
        /**
         * @brief Create a real constant
         *
         * Creates a real constant node from a high-precision real value.
         *
         * @param v Value (Real)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const Real &v); // CONST_REAL
        
        /**
         * @brief Create a real constant from double
         *
         * Creates a real constant node from a double value.
         *
         * @param v Value (double)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const double &v); // CONST_REAL
        
        /**
         * @brief Create a real constant from integer
         *
         * Creates a real constant node from an arbitrary-precision integer value.
         *
         * @param v Value (Integer)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const Integer &v); // CONST_REAL
        
        /**
         * @brief Create a string constant
         *
         * Creates a string constant node.
         *
         * @param v Value (string)
         * @return String constant node
         */
        std::shared_ptr<DAGNode> mkConstStr(const std::string &v); // CONST_Str
        
        /**
         * @brief Create a bit-vector constant
         *
         * Creates a bit-vector constant node with the given value and width.
         *
         * @param v Value (string)
         * @param width Width of the bit-vector
         * @return Bit-vector constant node
         */
        std::shared_ptr<DAGNode> mkConstBv(const std::string &v, const size_t& width); // CONST_BV
        
        /**
         * @brief Create a floating-point constant
         *
         * Creates a floating-point constant node with the given value and format.
         *
         * @param v Value (string)
         * @param e Exponent size
         * @param s Significand size
         * @return Floating-point constant node
         */
        std::shared_ptr<DAGNode> mkConstFp(const std::string &v, const size_t& e, const size_t& s); // CONST_FP
        
        /**
         * @brief Create a regular expression constant
         *
         * Creates a regular expression constant node.
         *
         * @param v Value (string)
         * @return Regular expression constant node
         */
        std::shared_ptr<DAGNode> mkConstReg(const std::string &v); // CONST_REG
        
        // VAR
        /**
         * @brief Create a variable
         *
         * Creates a variable node with the given sort and name.
         *
         * @param sort Sort
         * @param name Variable name
         * @return Variable node
         */
        std::shared_ptr<DAGNode> mkVar(const std::shared_ptr<Sort>& sort, const std::string &name); // VAR
        
        /**
         * @brief Create a temporary variable
         *
         * Creates a temporary variable node with the given sort.
         *
         * @param sort Sort
         * @return Temporary variable node
         */
        std::shared_ptr<DAGNode> mkTempVar(const std::shared_ptr<Sort>& sort); // TEMP_VAR
        
        /**
         * @brief Create a boolean variable
         *
         * Creates a boolean variable node with the given name.
         *
         * @param name Variable name
         * @return Boolean variable node
         */
        std::shared_ptr<DAGNode> mkVarBool(const std::string &name); // VAR_BOOL
        
        /**
         * @brief Create an integer variable
         *
         * Creates an integer variable node with the given name.
         *
         * @param name Variable name
         * @return Integer variable node
         */
        std::shared_ptr<DAGNode> mkVarInt(const std::string &name); // VAR_INT
        
        /**
         * @brief Create a real variable
         *
         * Creates a real variable node with the given name.
         *
         * @param name Variable name
         * @return Real variable node
         */
        std::shared_ptr<DAGNode> mkVarReal(const std::string &name); // VAR_REAL
        
        /**
         * @brief Create a bit-vector variable
         *
         * Creates a bit-vector variable node with the given name and width.
         *
         * @param name Variable name
         * @param width Width of the bit-vector
         * @return Bit-vector variable node
         */
        std::shared_ptr<DAGNode> mkVarBv(const std::string &name, const size_t& width); // VAR_BV
        
        /**
         * @brief Create a floating-point variable
         *
         * Creates a floating-point variable node with the given name and format.
         *
         * @param name Variable name
         * @param e Exponent size
         * @param s Significand size
         * @return Floating-point variable node
         */
        std::shared_ptr<DAGNode> mkVarFp(const std::string &name, const size_t& e, const size_t& s); // VAR_FP
        
        /**
         * @brief Create a string variable
         *
         * Creates a string variable node with the given name.
         *
         * @param name Variable name
         * @return String variable node
         */
        std::shared_ptr<DAGNode> mkVarStr(const std::string &name); // VAR_STR
        
        /**
         * @brief Create a regular expression variable
         *
         * Creates a regular expression variable node with the given name.
         *
         * @param name Variable name
         * @return Regular expression variable node
         */
        std::shared_ptr<DAGNode> mkVarReg(const std::string &name); // VAR_REG
        
        /**
         * @brief Create a function parameter variable
         *
         * Creates a function parameter variable node with the given sort and name.
         *
         * @param sort Sort
         * @param name Variable name
         * @return Function parameter variable node
         */
        std::shared_ptr<DAGNode> mkFunParamVar(std::shared_ptr<Sort> sort, const std::string &name); // FUN_PARAM_VAR
        
        /**
         * @brief Create an array
         *
         * Creates an array node with the given name, index sort, and element sort.
         *
         * @param name Array name
         * @param index Index sort
         * @param elem Element sort
         * @return Array node
         */
        std::shared_ptr<DAGNode> mkArray(const std::string &name, std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem); // ARRAY
        
        // BOOLEAN
        /**
         * @brief Create a not node
         * 
         * Creates a not node with the given parameter.
         * 
         * @param param Parameter
         * @return Not node
         */
        std::shared_ptr<DAGNode> mkNot(std::shared_ptr<DAGNode> param);
        
        /**
         * @brief Create an and node
         * 
         * Creates an and node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return And node
         */
        std::shared_ptr<DAGNode> mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an and node
         * 
         * Creates an and node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return And node
         */
        std::shared_ptr<DAGNode> mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an and node
         * 
         * Creates an and node with the given parameters.
         * 
         * @param params Parameters
         * @return And node
         */
        std::shared_ptr<DAGNode> mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an or node
         * 
         * Creates an or node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Or node
         */
        std::shared_ptr<DAGNode> mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an or node
         * 
         * Creates an or node with the given parameters.
         * 
         * @param params Parameters
         * @return Or node
         */
        std::shared_ptr<DAGNode> mkOr(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an implies node
         * 
         * Creates an implies node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Implies node
         */
        std::shared_ptr<DAGNode> mkImplies(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an implies node
         * 
         * Creates an implies node with the given parameters.
         * 
         * @param params Parameters
         * @return Implies node
         */
        std::shared_ptr<DAGNode> mkImplies(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an xor node
         * 
         * Creates an xor node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Xor node
         */
        std::shared_ptr<DAGNode> mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an xor node
         * 
         * Creates an xor node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Xor node
         */
        std::shared_ptr<DAGNode> mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an xor node
         * 
         * Creates an xor node with the given parameters.
         * 
         * @param params Parameters
         * @return Xor node
         */
        std::shared_ptr<DAGNode> mkXor(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an ite node
         * 
         * Creates an ite node with the given parameters.
         * 
         * @param cond Condition
         * @param l Left parameter
         * @param r Right parameter
         * @return Ite node
         */
        std::shared_ptr<DAGNode> mkIte(std::shared_ptr<DAGNode> cond, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an ite node
         * 
         * Creates an ite node with the given parameters.
         * 
         * @param params Parameters
         * @return Ite node
         */
        std::shared_ptr<DAGNode> mkIte(const std::vector<std::shared_ptr<DAGNode>> &params);
        // ARITHMATIC COMMON OPERATORS

        /**
         * @brief Create an add node
         * 
         * Creates an add node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Add node (l + r)
         */
        std::shared_ptr<DAGNode> mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an add node
         * 
         * Creates an add node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Add node (l + m + r)
         */
        std::shared_ptr<DAGNode> mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an add node
         * 
         * Creates an add node with the given parameters.
         * 
         * @param params Parameters
         * @return Add node (l + r + ...)
         */
        std::shared_ptr<DAGNode> mkAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        
        /**
         * @brief Create an mul node
         * 
         * Creates an mul node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Mul node (l * r)
         */
        std::shared_ptr<DAGNode> mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an mul node
         * 
         * Creates an mul node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Mul node (l * m * r) 
         */
        std::shared_ptr<DAGNode> mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an mul node
         *  
         * Creates an mul node with the given parameters.
         * 
         * @param params Parameters
         * @return Mul node (l * r * ...)
         */
        std::shared_ptr<DAGNode> mkMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        
        /**
         * @brief Create an iand node
         * 
         * Creates an iand node with the given parameters.
         * 
         * @param params Parameters
         * @return Iand node (l & r & ...)
         */
        std::shared_ptr<DAGNode> mkIand(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ... 
        
        /**
         * @brief Create an pow2 node
         * 
         * Creates an pow2 node with the given parameter.
         * 
         * @param param Parameter
         * @return Pow2 node (2^param)
         */
        std::shared_ptr<DAGNode> mkPow2(std::shared_ptr<DAGNode> param); // 2^param
        
        /**
         * @brief Create an pow node
         * 
         * Creates an pow node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Pow node (l^r)
         */
        std::shared_ptr<DAGNode> mkPow(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l^r
        
        /**
         * @brief Create an sub node
         * 
         * Creates an sub node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Sub node (l - r)
         */
        std::shared_ptr<DAGNode> mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an sub node
         * 
         * Creates an sub node with the given parameters.
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Sub node (l - m - r)
         */
        std::shared_ptr<DAGNode> mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an sub node
         * 
         * Creates an sub node with the given parameters.
         * 
         * @param params Parameters
         * @return Sub node (l - r - ...)
         */
        std::shared_ptr<DAGNode> mkSub(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an neg node
         * 
         * Creates an neg node with the given parameter.
         * 
         * @param param Parameter
         * @return Neg node (-param)
         */
        std::shared_ptr<DAGNode> mkNeg(std::shared_ptr<DAGNode> param); // -param
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @note This is the real division operator.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @note This is the real division operator.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDiv(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDivInt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @param params Parameters
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDivInt(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDivReal(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * Creates an div node with the given parameters.
         * 
         * @param params Parameters
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDivReal(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /** 
         * @brief Create an mod node
         * 
         * Creates an mod node with the given parameters.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Mod node (l % r)
         */
        std::shared_ptr<DAGNode> mkMod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create an abs node
         * 
         * Creates an abs node with the given parameter.
         * 
         * @param param Parameter
         * @return Abs node (|param|)
         */
        std::shared_ptr<DAGNode> mkAbs(std::shared_ptr<DAGNode> param); // |param|
        
        /**
         * @brief Create an sqrt node
         * 
         * Creates an sqrt node with the given parameter.
         *
         * @note assert(param >= 0) 
         *
         * @param param Parameter
         * @return Sqrt node (sqrt(param))
         */
        std::shared_ptr<DAGNode> mkSqrt(std::shared_ptr<DAGNode> param); // sqrt(param)
        
        /**
         * @brief Create an safesqrt node
         * 
         * Creates an safesqrt node with the given parameter.
         * 
         * @param param Parameter
         * @return Safesqrt node (safesqrt(param))
         */
        std::shared_ptr<DAGNode> mkSafeSqrt(std::shared_ptr<DAGNode> param); // safesqrt(param)
        
        /**
         * @brief Create an ceil node
         * 
         * Creates an ceil node with the given parameter.
         * 
         * @param param Parameter
         * @return Ceil node (ceil(param))
         */
        std::shared_ptr<DAGNode> mkCeil(std::shared_ptr<DAGNode> param); // ceil(param)
        
        /**
         * @brief Create an floor node
         * 
         * Creates an floor node with the given parameter.
         * 
         * @param param Parameter
         * @return Floor node (floor(param))
         */
        std::shared_ptr<DAGNode> mkFloor(std::shared_ptr<DAGNode> param); // floor(param)
        
        /**
         * @brief Create an round node
         * 
         * Creates an round node with the given parameter.
         * 
         * @param param Parameter
         * @return Round node (round(param))
         */
        std::shared_ptr<DAGNode> mkRound(std::shared_ptr<DAGNode> param); // round(param)
        
        // TRANSCENDENTAL ARITHMATIC
        /**
         * @brief Create an exp node
         * 
         * Creates an exp node with the given parameter.
         * 
         * @param param Parameter
         * @return Exp node (exp(param))
         */
        std::shared_ptr<DAGNode> mkExp(std::shared_ptr<DAGNode> param); // exp(param)
        
        /**
         * @brief Create an ln node
         * 
         * Creates an ln node with the given parameter.
         * 
         * @note assert(param > 0)
         * 
         * @param param Parameter
         * @return Ln node (ln(param))
         */
        std::shared_ptr<DAGNode> mkLn(std::shared_ptr<DAGNode> param); // ln(param)
        
        /**
         * @brief Create an lg node
         * 
         * Creates an lg node with the given parameter.
         * 
         * @note assert(param > 0)
         *
         * @param param Parameter
         * @return Lg node (lg(param))
         */
        std::shared_ptr<DAGNode> mkLg(std::shared_ptr<DAGNode> param); // lg(param)
        
        /**
         * @brief Create an lb node
         * 
         * Creates an lb node with the given parameter.
         * 
         * @note assert(param > 0)
         *
         * @param param Parameter
         * @return Lb node (lb(param))
         */
        std::shared_ptr<DAGNode> mkLb(std::shared_ptr<DAGNode> param); // lb(param)
        
        /**
         * @brief Create an log node
         * 
         * Creates an log node with the given parameters.
         * 
         * @note r is the base, l is the argument
         * @note assert(r > 0 && r != 1 && l > 0)
         *
         * @param l Left parameter
         * @param r Right parameter
         * @return Log node (log_r(l))
         */
        std::shared_ptr<DAGNode> mkLog(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // log_l(r)
        
        /**
         * @brief Create an sin node
         * 
         * Creates an sin node with the given parameter.
         * 
         * @param param Parameter
         * @return Sin node (sin(param))
         */
        std::shared_ptr<DAGNode> mkSin(std::shared_ptr<DAGNode> param); // sin(param)
        
        /**
         * @brief Create an cos node
         * 
         * Creates an cos node with the given parameter.
         * 
         * @param param Parameter
         * @return Cos node (cos(param))
         */
        std::shared_ptr<DAGNode> mkCos(std::shared_ptr<DAGNode> param); // cos(param)
        
        /**
         * @brief Create an sec node
         * 
         * Creates an sec node with the given parameter.
         * 
         * @param param Parameter
         * @return Sec node (sec(param))
         */
        std::shared_ptr<DAGNode> mkSec(std::shared_ptr<DAGNode> param); // sec(param)
        
        /**
         * @brief Create an csc node
         * 
         * Creates an csc node with the given parameter.
         * 
         * @param param Parameter
         * @return Csc node (csc(param))
         */
        std::shared_ptr<DAGNode> mkCsc(std::shared_ptr<DAGNode> param); // csc(param)
        
        /**
         * @brief Create an tan node
         * 
         * Creates an tan node with the given parameter.
         * 
         * @param param Parameter
         * @return Tan node (tan(param))
         */
        std::shared_ptr<DAGNode> mkTan(std::shared_ptr<DAGNode> param); // tan(param)
        
        /**
         * @brief Create a cot node
         * 
         * Creates a cot node with the given parameter.
         * 
         * @note assert(sin(param) != 0)
         * 
         * @param param Parameter
         * @return Cot node (cot(param))
         */
        std::shared_ptr<DAGNode> mkCot(std::shared_ptr<DAGNode> param); // cot(param)
        
        /**
         * @brief Create an asin node
         * 
         * Creates an asin node with the given parameter.
         * 
         * @note assert(param >= -1 && param <= 1)
         * 
         * @param param Parameter
         * @return Asin node (asin(param))
         */
        std::shared_ptr<DAGNode> mkAsin(std::shared_ptr<DAGNode> param); // asin(param)
        
        /**
         * @brief Create an acos node
         * 
         * Creates an acos node with the given parameter.
         * 
         * @note assert(param >= -1 && param <= 1)
         * 
         * @param param Parameter
         * @return Acos node (acos(param))
         */
        std::shared_ptr<DAGNode> mkAcos(std::shared_ptr<DAGNode> param); // acos(param)
        
        /**
         * @brief Create an asec node
         * 
         * Creates an asec node with the given parameter.
         * 
         * @note assert(param <= -1 || param >= 1)
         * 
         * @param param Parameter
         * @return Asec node (asec(param))
         */
        std::shared_ptr<DAGNode> mkAsec(std::shared_ptr<DAGNode> param); // asec(param)
        
        /**
         * @brief Create an acsc node
         * 
         * Creates an acsc node with the given parameter.
         * 
         * @note assert(param <= -1 || param >= 1)
         * 
         * @param param Parameter
         * @return Acsc node (acsc(param))
         */
        std::shared_ptr<DAGNode> mkAcsc(std::shared_ptr<DAGNode> param); // acsc(param)
        
        /**
         * @brief Create an atan node
         * 
         * Creates an atan node with the given parameter.
         * 
         * @param param Parameter
         * @return Atan node (atan(param))
         */
        std::shared_ptr<DAGNode> mkAtan(std::shared_ptr<DAGNode> param); // atan(param)
        
        /**
         * @brief Create an acot node
         * 
         * Creates an acot node with the given parameter.
         * 
         * @param param Parameter
         * @return Acot node (acot(param))
         */
        std::shared_ptr<DAGNode> mkAcot(std::shared_ptr<DAGNode> param); // acot(param)
        
        /**
         * @brief Create a sinh node
         * 
         * Creates a sinh node with the given parameter.
         * 
         * @param param Parameter
         * @return Sinh node (sinh(param))
         */
        std::shared_ptr<DAGNode> mkSinh(std::shared_ptr<DAGNode> param); // sinh(param)
        
        /**
         * @brief Create a cosh node
         * 
         * Creates a cosh node with the given parameter.
         * 
         * @param param Parameter
         * @return Cosh node (cosh(param))
         */
        std::shared_ptr<DAGNode> mkCosh(std::shared_ptr<DAGNode> param); // cosh(param)
        
        /**
         * @brief Create a tanh node
         * 
         * Creates a tanh node with the given parameter.
         * 
         * @param param Parameter
         * @return Tanh node (tanh(param))
         */
        std::shared_ptr<DAGNode> mkTanh(std::shared_ptr<DAGNode> param); // tanh(param)
        
        /**
         * @brief Create a sech node
         * 
         * Creates a sech node with the given parameter.
         * 
         * @param param Parameter
         * @return Sech node (sech(param))
         */
        std::shared_ptr<DAGNode> mkSech(std::shared_ptr<DAGNode> param); // sech(param)
        
        /**
         * @brief Create a csch node
         * 
         * Creates a csch node with the given parameter.
         * 
         * @note assert(param != 0)
         * 
         * @param param Parameter
         * @return Csch node (csch(param))
         */
        std::shared_ptr<DAGNode> mkCsch(std::shared_ptr<DAGNode> param); // csch(param)
        
        /**
         * @brief Create a coth node
         * 
         * Creates a coth node with the given parameter.
         * 
         * @note assert(param != 0)
         * 
         * @param param Parameter
         * @return Coth node (coth(param))
         */
        std::shared_ptr<DAGNode> mkCoth(std::shared_ptr<DAGNode> param); // coth(param)
        
        /**
         * @brief Create an asinh node
         * 
         * Creates an asinh node with the given parameter.
         * 
         * @param param Parameter
         * @return Asinh node (asinh(param))
         */
        std::shared_ptr<DAGNode> mkAsinh(std::shared_ptr<DAGNode> param); // asinh(param)
        
        /**
         * @brief Create an acosh node
         * 
         * Creates an acosh node with the given parameter.
         * 
         * @note assert(param >= 1)
         * 
         * @param param Parameter
         * @return Acosh node (acosh(param))
         */
        std::shared_ptr<DAGNode> mkAcosh(std::shared_ptr<DAGNode> param); // acosh(param)
        
        /**
         * @brief Create an atanh node
         * 
         * Creates an atanh node with the given parameter.
         * 
         * @note assert(param > -1 && param < 1)
         * 
         * @param param Parameter
         * @return Atanh node (atanh(param))
         */
        std::shared_ptr<DAGNode> mkAtanh(std::shared_ptr<DAGNode> param); // atanh(param)
        
        /**
         * @brief Create an asech node
         * 
         * Creates an asech node with the given parameter.
         * 
         * @note assert(param > 0 && param <= 1)
         * 
         * @param param Parameter
         * @return Asech node (asech(param))
         */
        std::shared_ptr<DAGNode> mkAsech(std::shared_ptr<DAGNode> param); // asech(param)
        
        /**
         * @brief Create an acsch node
         * 
         * Creates an acsch node with the given parameter.
         * 
         * @note assert(param != 0)
         * 
         * @param param Parameter
         * @return Acsch node (acsch(param))
         */
        std::shared_ptr<DAGNode> mkAcsch(std::shared_ptr<DAGNode> param); // acsch(param)
        
        /**
         * @brief Create an acoth node
         * 
         * Creates an acoth node with the given parameter.
         * 
         * @note assert(param < -1 || param > 1)
         * 
         * @param param Parameter
         * @return Acoth node (acoth(param))
         */
        std::shared_ptr<DAGNode> mkAcoth(std::shared_ptr<DAGNode> param); // acoth(param)
        
        /**
         * @brief Create an atan2 node
         * 
         * Creates an atan2 node with the given parameters.
         * 
         * @note Represents the angle in radians between the positive x-axis and the ray to point (r, l)
         * @note atan2(l, r) = atan(l/r) with appropriate quadrant adjustment
         * 
         * @param l Left parameter (y-coordinate)
         * @param r Right parameter (x-coordinate)
         * @return Atan2 node (atan2(l, r))
         */
        std::shared_ptr<DAGNode> mkAtan2(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        // ARITHMATIC COMP
        std::shared_ptr<DAGNode> mkLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkLe(const std::vector<std::shared_ptr<DAGNode>>& params); // l <= r
        std::shared_ptr<DAGNode> mkLt(const std::vector<std::shared_ptr<DAGNode>>& params); // l < r
        std::shared_ptr<DAGNode> mkGe(const std::vector<std::shared_ptr<DAGNode>>& params); // l >= r
        std::shared_ptr<DAGNode> mkGt(const std::vector<std::shared_ptr<DAGNode>>& params); // l > r
        // ARITHMATIC CONVERSION
        std::shared_ptr<DAGNode> mkToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkToReal(std::shared_ptr<DAGNode> param); // to_real(param)
        // ARITHMATIC PROPERTIES
        std::shared_ptr<DAGNode> mkIsInt(std::shared_ptr<DAGNode> param); // is_int(param)
        std::shared_ptr<DAGNode> mkIsDivisible(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // is_divisible(l, r)
        std::shared_ptr<DAGNode> mkIsPrime(std::shared_ptr<DAGNode> param); // is_prime(param)
        std::shared_ptr<DAGNode> mkIsEven(std::shared_ptr<DAGNode> param); // is_even(param)
        std::shared_ptr<DAGNode> mkIsOdd(std::shared_ptr<DAGNode> param); // is_odd(param)
        // ARITHMATIC CONSTANTS
        std::shared_ptr<DAGNode> mkPi(); // pi
        std::shared_ptr<DAGNode> mkE(); // e
        std::shared_ptr<DAGNode> mkInfinity(); // infinity
        std::shared_ptr<DAGNode> mkNan(); // nan
        std::shared_ptr<DAGNode> mkEpsilon(); // epsilon
        // ARITHMATIC FUNCTIONS
        // std::shared_ptr<DAGNode> mkSum(const std::vector<std::shared_ptr<DAGNode>> &params); // \Sigma params
        // std::shared_ptr<DAGNode> mkProd(const std::vector<std::shared_ptr<DAGNode>> &params); // \Prod params
        std::shared_ptr<DAGNode> mkGcd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // gcd(l, r)
        std::shared_ptr<DAGNode> mkLcm(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // lcm(l, r)
        std::shared_ptr<DAGNode> mkFact(std::shared_ptr<DAGNode> param); // factorial(param)
        // BITVECTOR COMMON OPERATORS
        std::shared_ptr<DAGNode> mkBvNot(std::shared_ptr<DAGNode> param); // ~param
        std::shared_ptr<DAGNode> mkBvAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l & r
        std::shared_ptr<DAGNode> mkBvAnd(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ...
        std::shared_ptr<DAGNode> mkBvOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l | r
        std::shared_ptr<DAGNode> mkBvOr(const std::vector<std::shared_ptr<DAGNode>> &params); // l | r | ...
        std::shared_ptr<DAGNode> mkBvXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l ^ r
        std::shared_ptr<DAGNode> mkBvXor(const std::vector<std::shared_ptr<DAGNode>> &params); // l ^ r ^ ...
        std::shared_ptr<DAGNode> mkBvNand(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l & r)
        std::shared_ptr<DAGNode> mkBvNand(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l & r & ...)
        std::shared_ptr<DAGNode> mkBvNor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l | r)
        std::shared_ptr<DAGNode> mkBvNor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l | r | ...)
        std::shared_ptr<DAGNode> mkBvXnor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l ^ r)
        std::shared_ptr<DAGNode> mkBvComp(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        std::shared_ptr<DAGNode> mkBvXnor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l ^ r ^ ...)
        std::shared_ptr<DAGNode> mkBvNeg(std::shared_ptr<DAGNode> param); // -param
        std::shared_ptr<DAGNode> mkBvAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l + r
        std::shared_ptr<DAGNode> mkBvAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkBvSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l - r
        std::shared_ptr<DAGNode> mkBvSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkBvMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        std::shared_ptr<DAGNode> mkBvMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        std::shared_ptr<DAGNode> mkBvUdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkBvUrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvUmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvSdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        std::shared_ptr<DAGNode> mkBvSrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvSmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkBvShl(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l << r
        std::shared_ptr<DAGNode> mkBvLshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        std::shared_ptr<DAGNode> mkBvAshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        std::shared_ptr<DAGNode> mkBvConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // l ++ r ++ ...
        std::shared_ptr<DAGNode> mkBvExtract(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l[r:s]
        std::shared_ptr<DAGNode> mkBvRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        std::shared_ptr<DAGNode> mkBvZeroExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l zero_extend r
        std::shared_ptr<DAGNode> mkBvSignExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l sign_extend r
        std::shared_ptr<DAGNode> mkBvRotateLeft(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <<< r
        std::shared_ptr<DAGNode> mkBvRotateRight(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >>> r
        // BITVECTOR COMP
        std::shared_ptr<DAGNode> mkBvUlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkBvUle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkBvUgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkBvUge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkBvSlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkBvSle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkBvSgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkBvSge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        // BITVECTOR CONVERSION
        std::shared_ptr<DAGNode> mkBvToNat(std::shared_ptr<DAGNode> param); // to_nat(param)
        std::shared_ptr<DAGNode> mkNatToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)
        std::shared_ptr<DAGNode> mkBvToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkIntToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)
        // FLOATING POINT COMMON OPERATORS
        std::shared_ptr<DAGNode> mkFpAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkFpSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkFpMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        std::shared_ptr<DAGNode> mkFpDiv(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        std::shared_ptr<DAGNode> mkFpAbs(std::shared_ptr<DAGNode> param); // |param|
        std::shared_ptr<DAGNode> mkFpNeg(std::shared_ptr<DAGNode> param); // -param
        std::shared_ptr<DAGNode> mkFpRem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        std::shared_ptr<DAGNode> mkFpFma(const std::vector<std::shared_ptr<DAGNode>> &params); // fma(a, b, c) = a * b + c
        std::shared_ptr<DAGNode> mkFpSqrt(std::shared_ptr<DAGNode> param); // sqrt(param)
        std::shared_ptr<DAGNode> mkFpRoundToIntegral(std::shared_ptr<DAGNode> param); // round_to_integral(param)
        std::shared_ptr<DAGNode> mkFpMin(const std::vector<std::shared_ptr<DAGNode>> &params); // min(params)
        std::shared_ptr<DAGNode> mkFpMax(const std::vector<std::shared_ptr<DAGNode>> &params); // max(params)
        // FLOATING POINT COMP
        std::shared_ptr<DAGNode> mkFpLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkFpLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkFpGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        std::shared_ptr<DAGNode> mkFpGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkFpEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        // FLOATING POINT CONVERSION
        std::shared_ptr<DAGNode> mkFpToUbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_ubv(param, size)
        std::shared_ptr<DAGNode> mkFpToSbv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_sbv(param, size)
        std::shared_ptr<DAGNode> mkFpToReal(std::shared_ptr<DAGNode> param); // to_real(param)
        std::shared_ptr<DAGNode> mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> param); // to_fp(eb, sb, param)
        // FLOATING POINT PROPERTIES
        std::shared_ptr<DAGNode> mkFpIsNormal(std::shared_ptr<DAGNode> param); // is_normal(param)
        std::shared_ptr<DAGNode> mkFpIsSubnormal(std::shared_ptr<DAGNode> param); // is_subnormal(param)
        std::shared_ptr<DAGNode> mkFpIsZero(std::shared_ptr<DAGNode> param); // is_zero(param)
        std::shared_ptr<DAGNode> mkFpIsInf(std::shared_ptr<DAGNode> param); // is_inf(param)
        std::shared_ptr<DAGNode> mkFpIsNan(std::shared_ptr<DAGNode> param); // is_nan(param)
        std::shared_ptr<DAGNode> mkFpIsNeg(std::shared_ptr<DAGNode> param); // is_neg(param)
        std::shared_ptr<DAGNode> mkFpIsPos(std::shared_ptr<DAGNode> param); // is_pos(param)
        // ARRAY
        std::shared_ptr<DAGNode> mkSelect(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l[r]
        std::shared_ptr<DAGNode> mkStore(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // l[r] = v
        // STRINGS COMMON OPERATORS
        std::shared_ptr<DAGNode> mkStrLen(std::shared_ptr<DAGNode> param); // len(param)
        std::shared_ptr<DAGNode> mkStrConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // param1 + param2 + ...
        std::shared_ptr<DAGNode> mkStrSubstr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l.substr(r, s)
        std::shared_ptr<DAGNode> mkStrPrefixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // prefixof(l, r)
        std::shared_ptr<DAGNode> mkStrSuffixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // suffixof(l, r)
        std::shared_ptr<DAGNode> mkStrIndexof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // indexof(l, r, s)
        std::shared_ptr<DAGNode> mkStrCharat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // charat(l, r)
        std::shared_ptr<DAGNode> mkStrUpdate(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // update(l, r, v)
        std::shared_ptr<DAGNode> mkStrReplace(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace(l, r, v)
        std::shared_ptr<DAGNode> mkStrReplaceAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace_all(l, r, v)
        std::shared_ptr<DAGNode> mkStrToLower(std::shared_ptr<DAGNode> param); // to_lower(param)
        std::shared_ptr<DAGNode> mkStrToUpper(std::shared_ptr<DAGNode> param); // to_upper(param)
        std::shared_ptr<DAGNode> mkStrRev(std::shared_ptr<DAGNode> param); // rev(param)
        std::shared_ptr<DAGNode> mkStrSplit(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // split(l, r)
        // STRINGS COMP
        std::shared_ptr<DAGNode> mkStrLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        std::shared_ptr<DAGNode> mkStrLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        std::shared_ptr<DAGNode> mkStrGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        std::shared_ptr<DAGNode> mkStrGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        // STRINGS PROPERTIES
        std::shared_ptr<DAGNode> mkStrInReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l in r
        std::shared_ptr<DAGNode> mkStrContains(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // contains(l, r)
        std::shared_ptr<DAGNode> mkStrIsDigit(std::shared_ptr<DAGNode> param); // is_digit(param)
        // STRINGS CONVERSION
        std::shared_ptr<DAGNode> mkStrFromInt(std::shared_ptr<DAGNode> param); // from_int(param)
        std::shared_ptr<DAGNode> mkStrToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        std::shared_ptr<DAGNode> mkStrToReg(std::shared_ptr<DAGNode> param); // to_reg(param)
        std::shared_ptr<DAGNode> mkStrToCode(std::shared_ptr<DAGNode> param); // to_code(param) assci code
        std::shared_ptr<DAGNode> mkStrFromCode(std::shared_ptr<DAGNode> param); // from_code(param) assci code
        // STRINGS RE CONSTANTS
        std::shared_ptr<DAGNode> mkRegNone(); // none
        std::shared_ptr<DAGNode> mkRegAll(); // all
        std::shared_ptr<DAGNode> mkRegAllChar(); // allchar
        // STRINGS RE COMMON OPERATORS
        std::shared_ptr<DAGNode> mkRegConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        std::shared_ptr<DAGNode> mkRegUnion(const std::vector<std::shared_ptr<DAGNode>> &params); // l | r | ...
        std::shared_ptr<DAGNode> mkRegInter(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ...
        std::shared_ptr<DAGNode> mkRegDiff(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        std::shared_ptr<DAGNode> mkRegStar(std::shared_ptr<DAGNode> param); // param*
        std::shared_ptr<DAGNode> mkRegPlus(std::shared_ptr<DAGNode> param); // param+
        std::shared_ptr<DAGNode> mkRegOpt(std::shared_ptr<DAGNode> param); // param?
        std::shared_ptr<DAGNode> mkRegRange(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l..r
        std::shared_ptr<DAGNode> mkRegRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // re.^n reg
        std::shared_ptr<DAGNode> mkRegLoop(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l{r,s}
        std::shared_ptr<DAGNode> mkRegComplement(std::shared_ptr<DAGNode> param); // ~param
        // STRINGS RE FUNCTIONS
        std::shared_ptr<DAGNode> mkReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace(l, r, v)
        std::shared_ptr<DAGNode> mkReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace_all(l, r, v)
        std::shared_ptr<DAGNode> mkIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // indexof(l, r)
        // LET 
        std::shared_ptr<DAGNode> mkLet(const std::vector<std::shared_ptr<DAGNode>> &params); // let((key1, val1), (key2, val2), ...)
        // QUANTIFIERS
        std::shared_ptr<DAGNode> mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort);
        std::shared_ptr<DAGNode> mkForall(const std::vector<std::shared_ptr<DAGNode>> &params); // forall((var1, sort1), (var2, sort2), ..., body)
        std::shared_ptr<DAGNode> mkExists(const std::vector<std::shared_ptr<DAGNode>> &params); // exists((var1, sort1), (var2, sort2), ..., body)
        // FUNCTION
        std::shared_ptr<DAGNode> mkApplyFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params); // static apply function, only (f p1 p2 ... pn) without substitution
        

        // parse smt-lib2 file
        bool 	                 parseSmtlib2File(const std::string filename);
        // // // parse model file
        // void 	            parseModel(std::string filename, boost::unordered_map<std::string, vType>& recs);

        std::shared_ptr<Sort>    mkSort(); // mk unique sort, TODO!!!! for example, bv, fp, and array
        int                      getArity(NODE_KIND k) const;

        // aux functions
        NODE_KIND                getAddOp(std::shared_ptr<Sort> sort); // mk unique add 
        std::shared_ptr<DAGNode> getZero(std::shared_ptr<Sort> sort); // mk unique zero

        // parse optimization
        // single_opt = (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>]) 
        //            | (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        void                             parseAssertSoft();
        // (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>       parseMaximize();
        // (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>       parseMinimize();
        // (maxsat <expr> [:id])
        std::shared_ptr<Objective>       parseMaxsat();
        // (minsat <expr> [:id])
        std::shared_ptr<Objective>       parseMinsat();
        std::shared_ptr<Objective>       parseSingleObj(const OPT_KIND& opt_type);
        std::shared_ptr<Objective>       parseMultiObj(const OPT_KIND& opt_type);
        // (define-objective <symbol> signle_opt [:id <symbol>])
        std::shared_ptr<Objective>       parseDefObj();
        // (lex-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseLexOpt();
        // (pareto-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseParetoOpt();
        // (box-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseBoxOpt();
        // (minmax (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseMinmax();
        // (maxmin (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>       parseMaxmin();
        // (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
        std::shared_ptr<Objective>       parseOptimize();
        KEYWORD                          attemptParseKeywords();

        
        // additional functions
        std::shared_ptr<DAGNode>                substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode>                substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited);
        
        // apply function
        std::shared_ptr<DAGNode>	            applyFun(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> & params);
        std::shared_ptr<DAGNode>	            applyFunPostOrder(std::shared_ptr<DAGNode> node, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params);
        // negate an atom
        std::shared_ptr<DAGNode>	            negateAtom(std::shared_ptr<DAGNode> atom);

        // evaluate: return true if the evaluation has changed the expression
        void                                    setEvaluatePrecision(mpfr_prec_t precision);
        mpfr_prec_t                             getEvaluatePrecision() const;
        void                                    setEvaluateUseFloating(bool use_floating);
        bool                                    getEvaluateUseFloating() const;
        std::shared_ptr<DAGNode>                evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model);
        std::shared_ptr<DAGNode>                evaluate(std::shared_ptr<DAGNode> expr, const Model &model);
        bool                                    evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model, std::shared_ptr<DAGNode> &result);

        // type conversion
        Real                                    toReal(std::shared_ptr<DAGNode> expr);
        Integer                                 toInt(std::shared_ptr<DAGNode> expr);
        bool                                    isZero(std::shared_ptr<DAGNode> expr);
        bool                                    isOne(std::shared_ptr<DAGNode> expr);

        // Format conversion
        void                                    collectAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_set<std::shared_ptr<DAGNode>>& atoms);
        std::shared_ptr<DAGNode>                replaceAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map);
        std::shared_ptr<DAGNode>                toTseitinCNF(std::shared_ptr<DAGNode> expr, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toCNF(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toCNF(std::vector<std::shared_ptr<DAGNode>> exprs);
        std::shared_ptr<DAGNode>                toDNF(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toDNF(std::vector<std::shared_ptr<DAGNode>> exprs);
        std::shared_ptr<DAGNode>                toNNF(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toNNF(std::shared_ptr<DAGNode> expr, bool is_not);
        std::shared_ptr<DAGNode>                toNNF(std::vector<std::shared_ptr<DAGNode>> exprs);

        // print
        std::string                             toString(std::shared_ptr<DAGNode> expr);
    private:
        // parse smt-lib2 file
        std::string	                            getSymbol();
        void 		                            scanToNextSymbol();
        void		                            parseLpar();
        void 		                            parseRpar();
        void		                            skipToRpar();
        std::string                             peekSymbol();


        CMD_TYPE	                            parseCommand();
        KEYWORD                                 parseKeyword();
        std::shared_ptr<Sort>	                parseSort();
        std::shared_ptr<DAGNode>		        parseExpr();
        std::shared_ptr<DAGNode>		        parseConstFunc(const std::string& s);
        std::shared_ptr<DAGNode>		        parseParamFunc(const std::string& f, const std::vector<std::shared_ptr<DAGNode>> &args, const std::vector<std::shared_ptr<DAGNode>> &params);
        std::shared_ptr<DAGNode>		        parseOper(const std::string& s, const std::vector<std::shared_ptr<DAGNode>> &params);
        std::vector<std::shared_ptr<DAGNode>>	parseParams();
        std::shared_ptr<DAGNode>		        parseLet();
        std::string                             parseGroup();
        std::string                             parseWeight();
        void                                    parseQuant(const std::string& type);
        
        // auxilary functions
        std::shared_ptr<DAGNode>	            bindLetVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>	            bindFunVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        // conversion
        std::shared_ptr<DAGNode>                replaceAtoms(std::shared_ptr<DAGNode> expr, 
                                                            boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map, 
                                                            boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, 
                                                            bool& is_changed);
        std::shared_ptr<DAGNode>                toTseitinCNF(std::shared_ptr<DAGNode> expr, 
                                                            boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, 
                                                            std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinXor(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinEq(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinDistinct(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toDNFEliminateAll(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toDNFEliminateAll(std::shared_ptr<DAGNode> expr,
                                                                   boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited,
                                                                   bool& is_changed);
        std::shared_ptr<DAGNode>                toDNFEliminateXOR(const std::vector<std::shared_ptr<DAGNode>>& children);
        std::shared_ptr<DAGNode>                toDNFEliminateEq(const std::vector<std::shared_ptr<DAGNode>>& children);
        std::shared_ptr<DAGNode>                toDNFEliminateDistinct(const std::vector<std::shared_ptr<DAGNode>>& children);

        std::shared_ptr<DAGNode>                applyDNFDistributiveLaw(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                applyDNFDistributiveLawRec(std::shared_ptr<DAGNode> expr,
                                                                         boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited);
        std::shared_ptr<DAGNode>                flattenDNF(std::shared_ptr<DAGNode> expr);
        
        //errors & warnings
        // mk errror node
        std::shared_ptr<DAGNode>	            mkErr(const ERROR_TYPE t);
        // error/warning information
        void 		err_all(const ERROR_TYPE e, const std::string s = "", const size_t ln = 0) const;
        void 		err_all(const std::shared_ptr<DAGNode> e, const std::string s = "", const size_t ln = 0) const;

        void 		err_unexp_eof() const;
        void 		err_sym_mis(const std::string mis, const size_t ln) const;
        void 		err_sym_mis(const std::string mis, const std::string nm, const size_t ln) const;
        void 		err_unkwn_sym(const std::string nm, const size_t ln) const;
        void 		err_param_mis(const std::string nm, const size_t ln) const;
        void 		err_param_nbool(const std::string nm, const size_t ln) const;
        void 		err_param_nnum(const std::string nm, const size_t ln) const;
        void 		err_param_nsame(const std::string nm, const size_t ln) const;
        void 		err_logic(const std::string nm, const size_t ln) const;
        void 		err_mul_decl(const std::string nm, const size_t ln) const;
        void 		err_mul_def(const std::string nm, const size_t ln) const;
        void 		err_zero_divisor(const size_t ln) const;
        void        err_arity_mis(const std::string nm, const size_t ln) const;
        void        err_keyword(const std::string nm, const size_t ln) const;
        void        err_type_mis(const std::string nm, const size_t ln) const;
        void        err_neg_param(const size_t ln) const;

        void		err_open_file(const std::string) const;

        void 		warn_cmd_nsup(const std::string nm, const size_t ln) const;

        // collect atoms
        void        collectAtoms(std::shared_ptr<DAGNode> expr, boost::unordered_set<std::shared_ptr<DAGNode>>& atoms, boost::unordered_set<std::shared_ptr<DAGNode>>& visited);
        // evaluate functions
        bool		evaluateSimpleOp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result, NODE_KIND op);
        bool		evaluateAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDistinct(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIte(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDivInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDivReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);   
        bool		evaluateMod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluatePow(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluatePow2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSafeSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCeil(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFloor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRound(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateExp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLn(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLog(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLb(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateTan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateTanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtan2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsDivisible(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsPrime(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsEven(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsOdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGcd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLcm(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFact(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvXnor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvComp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSmod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvShl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvLshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvToNat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNatToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvIntToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpDiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpFma(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpRem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpRoundToIntegral(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToUbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToSbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToFp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsSubnormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsZero(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsInf(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsPos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSelect(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStore(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLen(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSubstr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrPrefixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSuffixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrIndexof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrCharat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrUpdate(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrReplace(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrReplaceAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToLower(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToUpper(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrRev(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrInReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrContains(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrIsDigit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrFromInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrFromCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegUnion(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegInter(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegDiff(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegStar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegPlus(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegOpt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegRange(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegComplement(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateApplyFun(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
    };


    // smart pointer
    typedef std::shared_ptr<Parser> ParserPtr;
    ParserPtr newParser();
    ParserPtr newParser(const std::string& filename);
}
#endif
