/* -*- Source -*-
 *
 * An SMT/OMT Parser (Base part)
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

#include "parser.h"
#include <queue>
#include <stack>

namespace SMTParser{

	Parser::Parser(){
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;
		temp_var_counter = 0;

		node_list.emplace_back(FALSE_NODE);
		node_list.emplace_back(TRUE_NODE);
		node_list.emplace_back(UNKNOWN_NODE);
		node_list.emplace_back(E_NODE);
		node_list.emplace_back(PI_NODE);
		node_list.emplace_back(STR_INF_NODE);
		node_list.emplace_back(STR_POS_INF_NODE);
		node_list.emplace_back(STR_NEG_INF_NODE);
		node_list.emplace_back(INT_INF_NODE);
		node_list.emplace_back(INT_POS_INF_NODE);
		node_list.emplace_back(INT_NEG_INF_NODE);
		node_list.emplace_back(REAL_INF_NODE);
		node_list.emplace_back(REAL_POS_INF_NODE);
		node_list.emplace_back(REAL_NEG_INF_NODE);
		node_list.emplace_back(NAN_NODE);
		node_list.emplace_back(EPSILON_NODE);
		node_list.emplace_back(POS_EPSILON_NODE);
		node_list.emplace_back(NEG_EPSILON_NODE);
		options = std::make_shared<GlobalOptions>();
	}

	
	bool Parser::parse(const std::string& filename){
		return parseSmtlib2File(filename);
	}

	Parser::Parser(const std::string& filename) {
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;
		temp_var_counter = 0;

		node_list.emplace_back(FALSE_NODE);
		node_list.emplace_back(TRUE_NODE);
		node_list.emplace_back(UNKNOWN_NODE);
		node_list.emplace_back(E_NODE);
		node_list.emplace_back(PI_NODE);
		node_list.emplace_back(STR_INF_NODE);
		node_list.emplace_back(STR_POS_INF_NODE);
		node_list.emplace_back(STR_NEG_INF_NODE);
		node_list.emplace_back(INT_INF_NODE);
		node_list.emplace_back(INT_POS_INF_NODE);
		node_list.emplace_back(INT_NEG_INF_NODE);
		node_list.emplace_back(REAL_INF_NODE);
		node_list.emplace_back(REAL_POS_INF_NODE);
		node_list.emplace_back(NAN_NODE);
		node_list.emplace_back(EPSILON_NODE);
		node_list.emplace_back(POS_EPSILON_NODE);
		node_list.emplace_back(NEG_EPSILON_NODE);

		options = std::make_shared<GlobalOptions>();

		parseSmtlib2File(filename);
	}

	Parser::~Parser() {	}

	// to solver
	std::vector<std::shared_ptr<DAGNode>> Parser::getAssertions() const{
		return assertions;
	}
	boost::unordered_map<std::string, boost::unordered_set<size_t>> Parser::getGroupedAssertions() const{
		return assertion_groups;
	}
	std::vector<std::vector<std::shared_ptr<DAGNode>>> Parser::getAssumptions() const{
		return assumptions;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getSoftAssertions() const{
		return soft_assertions;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getSoftWeights() const{
		return soft_weights;
	}
	boost::unordered_map<std::string, boost::unordered_set<size_t>> Parser::getGroupedSoftAssertions() const{
		return soft_assertion_groups;
	}
	std::vector<std::shared_ptr<Objective>> Parser::getObjectives() const{
		return objectives;
	}
	std::shared_ptr<GlobalOptions> Parser::getOptions() const{
		return options;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		for(auto& var : var_names){
			vars.emplace_back(node_list[var.second]);
		}
		for(auto& var : temp_var_names){
			vars.emplace_back(node_list[var.second]);
		}
		return vars;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getDeclaredVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		for(auto& var : var_names){
			vars.emplace_back(node_list[var.second]);
		}
		return vars;
	}
	std::shared_ptr<DAGNode> Parser::getVariable(const std::string& var_name){
		if(var_names.find(var_name) != var_names.end()){
			return node_list[var_names.at(var_name)];
		}
		else if(temp_var_names.find(var_name) != temp_var_names.end()){
			return node_list[temp_var_names.at(var_name)];
		}
		return NULL_NODE;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getFunctions() const{
		std::vector<std::shared_ptr<DAGNode>> funs;
		for(auto fun : function_names){
			funs.emplace_back(fun_key_map.at(fun));
		}
		return funs;
	}
	void Parser::setEvaluatePrecision(mpfr_prec_t precision){
		options->setEvaluatePrecision(precision);
	}
	mpfr_prec_t Parser::getEvaluatePrecision() const{
		return options->getEvaluatePrecision();
	}
	void Parser::setEvaluateUseFloating(bool use_floating){
		options->setEvaluateUseFloating(use_floating);
	}
	bool Parser::getEvaluateUseFloating() const{
		return options->getEvaluateUseFloating();
	}
	Real Parser::toReal(std::shared_ptr<DAGNode> expr){
		cassert(expr->isCReal() || expr->isCInt(), "Cannot convert non-constant expression to real");
		if(expr->isPi()) return Real::pi(getEvaluatePrecision());
		if(expr->isE()) return Real::e(getEvaluatePrecision());
		return expr->getValue()->getNumberValue().toReal(getEvaluatePrecision());
	}
	Integer Parser::toInt(std::shared_ptr<DAGNode> expr){
		cassert(expr->isCInt(), "Cannot convert non-integer expression to integer");
		return expr->getValue()->getNumberValue().toInteger();
	}
	bool Parser::isZero(std::shared_ptr<DAGNode> expr){
		if(expr->isCReal()) return toReal(expr) == 0.0;
		if(expr->isCInt()) return toInt(expr) == 0;
		return false;
	}
	bool Parser::isOne(std::shared_ptr<DAGNode> expr){
		if(expr->isCReal()) return toReal(expr) == 1.0;
		if(expr->isCInt()) return toInt(expr) == 1;
		return false;
	}

	// parse smt-lib2 file
	std::string Parser::getSymbol() {

		char *beg = bufptr;
		bool in_scientific_notation = false;
		bool has_open_bracket = false;
		int bracket_level = 0;

		// first char was already scanned
		bufptr++;

		// while not eof	
		while (*bufptr != 0) {

			switch (scan_mode) {
			case SCAN_MODE::SM_SYMBOL:
				// check if in scientific notation mode
				if (!in_scientific_notation) {
					// check if current symbol is the start of scientific notation
					std::string current(beg, bufptr - beg);
					size_t e_pos = current.find_first_of("Ee");
					if (e_pos != std::string::npos && e_pos > 0 && e_pos == current.size() - 1) {
						// check if the part before E is a valid real number
						std::string mantissa = current.substr(0, e_pos);
						if (isRealUtil(mantissa)) {
							// confirm the start of scientific notation
							in_scientific_notation = true;
						}
					}
				}

				// if in scientific notation mode
				if (in_scientific_notation) {
					// handle left parenthesis
					if (*bufptr == '(') {
						has_open_bracket = true;
						bracket_level++;
						bufptr++;
						continue;
					}
					// handle right parenthesis
					else if (*bufptr == ')' && has_open_bracket) {
						bracket_level--;
						if (bracket_level == 0) {
							// right parenthesis matched, end scientific notation
							bufptr++;
							std::string tmp_s(beg, bufptr - beg);
							scanToNextSymbol();
							return tmp_s;
						}
						bufptr++;
						continue;
					}
					// handle space, allow space in scientific notation mode
					else if (isblank(*bufptr)) {
						bufptr++;
						continue;
					}
					// if encounter newline or other special characters, end scientific notation mode
					else if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f' ||
							 *bufptr == ';' || *bufptr == '|' || *bufptr == '"') {
						in_scientific_notation = false;
						// return the parsed part
						std::string tmp_s(beg, bufptr - beg);
						return tmp_s;
					}
				}
				// normal symbol parsing
				else {
					if (isblank(*bufptr)) {
						// out of symbol mode by ' ' and \t
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						bufptr++;
						scanToNextSymbol();
						return tmp_s;
					}
					else if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
						line_number++;
						// out of symbol mode by '\n', '\r', '\v' and '\f'
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						bufptr++;
						scanToNextSymbol();
						return tmp_s;
					}
					else if (*bufptr == ';' || *bufptr == '|' || *bufptr == '"' || *bufptr == '(' || *bufptr == ')') {
						// out of symbol mode by ';', '|', '"', '(' and ')'
						std::string tmp_s(beg, bufptr - beg);
						return tmp_s;
					}
				}
				break;

			case SCAN_MODE::SM_COMP_SYM:
				if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
					line_number++;
				}
				else if (*bufptr == '|') {
					// out of complicated symbol mode
					bufptr++;
					std::string tmp_s(beg, bufptr - beg);
					// skip space
					scanToNextSymbol();
					return tmp_s;
				}
				break;

			case SCAN_MODE::SM_STRING:
				if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
					line_number++;
				}
				else if (*bufptr == '"') {
					// out of std::string mode
					bufptr++;
					std::string tmp_s(beg, bufptr - beg);
					// skip space
					scanToNextSymbol();
					return tmp_s;
				}
				break;

			default:
				cassert(false, "Invalid scan mode");
			}

			// go next char
			bufptr++;
		}

		err_unexp_eof();

		return NULL;
	}

	void Parser::scanToNextSymbol() {

		// init scan mode
		scan_mode = SCAN_MODE::SM_COMMON;

		// while not eof
		while (*bufptr != 0) {

			if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {

				line_number++;

				// out of comment mode
				if (scan_mode == SCAN_MODE::SM_COMMENT) scan_mode = SCAN_MODE::SM_COMMON;

			}
			else if (scan_mode == SCAN_MODE::SM_COMMON && !isblank(*bufptr)) {

				switch (*bufptr) {
				case ';':
					// encounter comment
					scan_mode = SCAN_MODE::SM_COMMENT;
					break;
				case '|':
					// encounter next complicated symbol
					scan_mode = SCAN_MODE::SM_COMP_SYM;
					return;
				case '"':
					// encounter next std::string
					scan_mode = SCAN_MODE::SM_STRING;
					return;
				default:
					// encounter next symbol
					scan_mode = SCAN_MODE::SM_SYMBOL;
					return;
				}

			}

			// go next char
			bufptr++;
		}

	}

	void Parser::parseLpar() {
		if (*bufptr == '(') {
			bufptr++;
			scanToNextSymbol();
		}
		else {
			err_sym_mis("(", line_number);
		}
	}

	void Parser::parseRpar() {
		if (*bufptr == ')') {
			bufptr++;
			scanToNextSymbol();
		}
		else {
			err_sym_mis(")", line_number);
		}
	}

	void Parser::skipToRpar() {

		// skip to next right parenthesis with same depth	
		scan_mode = SCAN_MODE::SM_COMMON;
		size_t level = 0;

		while (*bufptr != 0) {

			if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
				// new line
				line_number++;
				if (scan_mode == SCAN_MODE::SM_COMMENT)
					scan_mode = SCAN_MODE::SM_COMMON;
			}
			else if (scan_mode == SCAN_MODE::SM_COMMON) {

				if (*bufptr == '(') level++;
				else if (*bufptr == ')') {
					if (level == 0) return;
					else level--;
				}
				else if (*bufptr == ';')
					scan_mode = SCAN_MODE::SM_COMMENT;
				else if (*bufptr == '|')
					scan_mode = SCAN_MODE::SM_COMP_SYM;
				else if (*bufptr == '"')
					scan_mode = SCAN_MODE::SM_STRING;

			}
			else if (scan_mode == SCAN_MODE::SM_COMP_SYM && *bufptr == '|')
				scan_mode = SCAN_MODE::SM_COMMON;
			else if (scan_mode == SCAN_MODE::SM_STRING && *bufptr == '"')
				scan_mode = SCAN_MODE::SM_COMMON;

			// go to next char
			bufptr++;
		}

	}

	// parse smt-lib2 file
	bool Parser::parseSmtlib2File(const std::string filename) {

		/*
		load file
		*/
		std::ifstream fin(filename, std::ifstream::binary);

		if (!fin) {
			err_open_file(filename);
		}

		fin.seekg(0, std::ios::end);
		buflen = (long)fin.tellg();
		fin.seekg(0, std::ios::beg);

		buffer = new char[buflen + 1];
		fin.read(buffer, buflen);
		buffer[buflen] = 0;

		fin.close();


		/*
		parse command
		*/
		bufptr = buffer;
		if (buflen > 0) line_number = 1;

		// skip to first symbol;
		scanToNextSymbol();

		while (*bufptr) {
			parseLpar();
			if (parseCommand() == CMD_TYPE::CT_EXIT) break;
			parseRpar();
		}
		bufptr = nullptr;
		delete[] buffer;
		return true;
	}

	bool Parser::parseStr(const std::string& constraint) {
		buffer = strdup(constraint.c_str());
		buflen = constraint.length();
		bufptr = buffer;
		if (buflen > 0) line_number = 1;
		scanToNextSymbol();
		while (*bufptr) {
			parseLpar();
			if (parseCommand() == CMD_TYPE::CT_EXIT) break;
			parseRpar();
		}
		bufptr = nullptr;
		free(buffer);
		return true;
	}

	bool Parser::assert(const std::string& constraint) {
		std::shared_ptr<DAGNode> expr = mkExpr(constraint);
		assertions.emplace_back(expr);
		return true;
	}

	bool Parser::assert(std::shared_ptr<DAGNode> node) {
		assertions.emplace_back(node);
		return true;
	}

	std::shared_ptr<DAGNode> Parser::mkExpr(const std::string& expression) {
		buffer = strdup(expression.c_str());
		buflen = expression.length();
		bufptr = buffer;
		if (buflen > 0) line_number = 1;
		scanToNextSymbol();
		std::shared_ptr<DAGNode> expr = parseExpr();
		bufptr = nullptr;
		free(buffer);
		return expr;
	}
	

	KEYWORD Parser::parseKeyword(){
		
		size_t key_ln = line_number;
		std::string key = getSymbol();
		if(key == ":id"){
			return KEYWORD::KW_ID;
		}
		else if(key == ":weight"){
			return KEYWORD::KW_WEIGHT;
		}
		else if (key == ":comp"){
			return KEYWORD::KW_COMP;
		}
		else if (key == ":epsilon"){
			return KEYWORD::KW_EPSILON;
		}
		else if(key == ":M"){
			return KEYWORD::KW_M;
		}
		else{
			err_unkwn_sym(key, key_ln);
		}
		return KEYWORD::KW_NULL;
	}

	CMD_TYPE Parser::parseCommand() {

		size_t command_ln = line_number;
		std::string command = getSymbol();

		// (assert <expr>) or (assert <expr> [:id <symbol>])
		if (command == "assert") {
			std::string grp_id = "";
			KEYWORD key = attemptParseKeywords();
			if(key == KEYWORD::KW_ID){
				// (assert [:id <symbol>] <expr>)
				grp_id = getSymbol();
			}
			std::shared_ptr<DAGNode> assert_expr = parseExpr();
			size_t index = assertions.size();
			assertions.emplace_back(assert_expr);
			// 
			if(grp_id == ""){
				KEYWORD key_ = attemptParseKeywords();
				if(key_ == KEYWORD::KW_ID){
					// (assert <expr> [:id <symbol>])
					grp_id = getSymbol();
				}
			}
			// if grp_id is not empty, insert to assertion_groups
			if(grp_id != ""){
				if(assertion_groups.find(grp_id) == assertion_groups.end()){
					assertion_groups.insert(std::pair<std::string, boost::unordered_set<size_t>>(grp_id, {index}));
				}
				else{
					assertion_groups[grp_id].insert(index);
				}
			}
			skipToRpar();
			return CMD_TYPE::CT_ASSERT;
		}
		// (assert-soft <expr> [:weight <numeral>] [:id <symbol>])
		if (command == "assert-soft") {
			parseAssertSoft();
			skipToRpar();
			return CMD_TYPE::CT_ASSERT_SOFT;
		}

		// (check-sat)
		if (command == "check-sat") {
			options->check_sat = true;
			skipToRpar();
			return CMD_TYPE::CT_CHECK_SAT;
		}

		// (check-sat-assuming (a1, ..., an)), maybe for future incremental mode.
		if (command == "check-sat-assuming") {
			//parse (a1, ..., an)
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> cur_assumptions;
			while (*bufptr != ')') {
				std::shared_ptr<DAGNode> assump = parseExpr();
				cur_assumptions.emplace_back(assump);
			}
			assumptions.emplace_back(cur_assumptions);
			skipToRpar();
			return CMD_TYPE::CT_CHECK_SAT_ASSUMING;
		}

		// (declare-const <symbol> <sort>)
		if (command == "declare-const") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			// get returned type
			std::shared_ptr<DAGNode> res = nullptr;
			std::shared_ptr<Sort> sort = parseSort();
			res = mkVar(sort, name);

			// multiple declarations
			if (res->isErr()) err_all(res, name, name_ln);
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_CONST;
		}

		// (declare-fun <symbol> (<sort>*) <sort>)
		if (command == "declare-fun") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			// (declare-fun <symbol> (<sort>*) <sort>)
			//                       ^
			parseLpar();
			// (declare-fun <symbol> (<sort>*) <sort>)
			//                               ^
			std::shared_ptr<DAGNode> res = nullptr;
			if(*bufptr == ')'){
				// (declare-fun <symbol> () <sort>)
				parseRpar();
				std::shared_ptr<Sort> out_sort = parseSort();
				res = mkVar(out_sort, name);
			}
			else{
				// (declare-fun <symbol> (<sort>+) <sort>)
				std::vector<std::shared_ptr<Sort>> params;
				while(*bufptr != ')'){
					params.emplace_back(parseSort());
				}
				parseRpar();
				std::shared_ptr<Sort> out_sort = parseSort();
				res = mkFuncDec(name, params, out_sort);
			}

			//multiple declarations
			if (res->isErr()) err_all(res, name, name_ln);
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_FUN;
		}

		// (declare-sort <symbol> <numeral>)
		if (command == "declare-sort") {
			//get name
			std::string name = getSymbol();

			//get numeral
			std::string numeral = getSymbol();
			size_t num = std::stoi(numeral);

			// make sort
			std::shared_ptr<Sort> sort = mkSortDec(name, num);
			sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(name, sort));
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_SORT;
		}

		//(define-fun <symbol> ((<symbol> <sort>)*) <sort> <expr>)
		if (command == "define-fun") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			if(fun_key_map.find(name) != fun_key_map.end()){
				std::shared_ptr<DAGNode> check_fun = fun_key_map[name];
				if(check_fun->getKind() == NODE_KIND::NT_FUNC_DEF){
					err_mul_def(name, name_ln);
				}
				return CMD_TYPE::CT_DEFINE_FUN;
			}
			// keep the function name with the same order
			function_names.emplace_back(name);

			// parse ((x Int))
			//       ^
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> params;
			std::vector<std::string> key_list;
			while(*bufptr!=')'){ // there are still (x Int) left.
				// (x Int)
				// ^
				parseLpar();
				std::string pname = getSymbol();
				std::shared_ptr<Sort> ptype = parseSort();
				key_list.emplace_back(pname);
				std::shared_ptr<DAGNode> expr = nullptr;
				expr = mkFunParamVar(ptype, pname);
				// multiple declarations
				if(fun_var_map.find(pname) != fun_var_map.end()){
					err_mul_decl(pname, line_number);
				}
				else{
					fun_var_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(pname, expr));
					params.emplace_back(expr);
				}
				// (x Int)
				//		 ^
				parseRpar();
			}
			
			//(define-fun <symbol> ((<symbol> <sort>)*) <sort> <expr>)
			//					                      ^
			parseRpar();

			//get returned type
			std::shared_ptr<Sort> out_sort = parseSort();
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::shared_ptr<DAGNode> res = mkFuncDef(name, params, out_sort, func_body);
			skipToRpar();

			//remove key bindings: for let uses local variables. 
			while (key_list.size() > 0) {
				fun_var_map.erase(key_list.back());
				key_list.pop_back();
			}
			
			return CMD_TYPE::CT_DEFINE_FUN;
		}

		// (define-fun-rec <symbol> ((<symbol> <sort>)*) <sort> <expr>)
		// recursive function definition
		if (command == "define-fun-rec") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_FUN_REC;
		}

		if (command == "define-funs-rec") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_FUNS_REC;
		}

		// (define-sort <symbol> (<symbol>*) <sort>)
		// <symbol>* is a list of symbols that represent template parameters.
		// for example, (define-sort List (T) (List T))
		// T is a template parameter.
		// then (define-sort IntList () (List Int)) is a valid command.
		// NOTE: It is in a conflict with the (declare-sort ...) command, because the final parameter is <sort> which is only one sort, it will be conflict when 
		// (declare-sort <symbol> <numeral>) and <numeral> > 1
		// so, we changed it to
		// (define-sort <symbol> (<symbol>*) (<sort>*)) which the number of <sort>* matches <numeral>
		// but now, not support
		if (command == "define-sort") {
			// ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_SORT;
		}

		if (command == "echo") {
			// ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_ECHO;
		}

		// (exit)
		if (command == "exit") {
			skipToRpar();
			return CMD_TYPE::CT_EXIT;
		}

		// (get-assertions)
		// but used in interactive mode, so ignore it.
		if (command == "get-assertions") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_ASSERTIONS;
		}

		if (command == "get-assignment") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_ASSIGNMENT;
		}

		if (command == "get-info") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_INFO;
		}

		if (command == "get-option") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_OPTION;
		}

		if (command == "get-model") {
			//ignore
			options->get_model = true;
			skipToRpar();
			return CMD_TYPE::CT_GET_MODEL;
		}

		if (command == "get-option") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_OPTION;
		}

		if (command == "get-proof") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_PROOF;
		}

		if (command == "get-unsat-assumptions") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_UNSAT_ASSUMPTIONS;
		}

		if (command == "get-unsat-core") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_UNSAT_CORE;
		}

		if (command == "get-value") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_VALUE;
		}

		if (command == "pop") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_POP;
		}

		if (command == "push") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_PUSH;
		}

		if (command == "reset") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_RESET;
		}

		if (command == "reset-assertions") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_RESET_ASSERTIONS;
		}

		//<attribute ::= <keyword> | <keyword> <attribute_value>
		//(set-info <attribute>)
		if (command == "set-info") {
			skipToRpar();
			return CMD_TYPE::CT_SET_INFO;
		}

		//(set-logic <symbol>)
		if (command == "set-logic") {
			size_t type_ln = line_number;
			std::string type = getSymbol();
			bool is_valid = options->setLogic(type);
			if(!is_valid){
				err_unkwn_sym(type, type_ln);
			}

			return CMD_TYPE::CT_SET_LOGIC;
		}

		//<option ::= <attribute>
		//(set-option <option>)
		if (command == "set-option") {
			skipToRpar();
			return CMD_TYPE::CT_SET_OPTION;
		}
		
		// quantifier
		// (quantifier ((<symbol> <sort>)+) <expr>)
		if(command == "exists") {
			parseQuant("exists");
			skipToRpar();
			return CMD_TYPE::CT_EXISTS;
		}
		if(command == "forall") {
			parseQuant("forall");
			skipToRpar();
			return CMD_TYPE::CT_FORALL;
		}

		// optimization
		if(command == "get-objectives"){
			options->get_objectives = true;
			skipToRpar();
			return CMD_TYPE::CT_GET_OBJECTIVES;
		}

		// (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "maximize"){
			parseMaximize();
			skipToRpar();
			return CMD_TYPE::CT_MAXIMIZE;
		}

		// (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "minimize"){
			parseMinimize();
			skipToRpar();
			return CMD_TYPE::CT_MINIMIZE;
		}

		// multi-objective optimization
		// (define-objective <symbol> <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "define-objective"){
			parseDefObj();
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_OBJ;
		}
		// (lex-optimize (<symbol>+) [:id <symbol>])
		if(command == "lex-optimize"){
			parseLexOpt();
			skipToRpar();
			return CMD_TYPE::CT_LEX_OPTIMIZE;
		}
		// (pareto-optimize (<symbol>+) [:id <symbol>])
		if(command == "pareto-optimize"){
			parseParetoOpt();
			skipToRpar();
			return CMD_TYPE::CT_PARETO_OPTIMIZE;
		}
		// (box-optimize (<symbol>+) [:id <symbol>])
		if(command == "box-optimize"){
			parseBoxOpt();
			skipToRpar();
			return CMD_TYPE::CT_BOX_OPTIMIZE;
		}
		// (minmax (<symbol>+) [:id <symbol>])
		if(command == "minmax"){
			parseMinmax();
			skipToRpar();
			return CMD_TYPE::CT_MINMAX;
		}
		// (maxmin (<symbol>+) [:id <symbol>])
		if(command == "maxmin"){
			parseMaxmin();
			skipToRpar();
			return CMD_TYPE::CT_MAXMIN;
		}
		// (maxsat [:id <symbol>])
		if(command == "maxsat"){
			parseMaxsat();
			skipToRpar();
			return CMD_TYPE::CT_MAXSAT;
		}
		// (minsat [:id <symbol>])
		if(command == "minsat"){
			parseMinsat();
			skipToRpar();
			return CMD_TYPE::CT_MINSAT;
		}
		// (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
		if(command == "optimize"){
			parseOptimize();
			skipToRpar();
			return CMD_TYPE::CT_OPTIMIZE;
		}

		err_unkwn_sym(command, command_ln);

		return CMD_TYPE::CT_UNKNOWN;

	}

	// expr ::= const | func | (<identifier> <expr>+)
	std::shared_ptr<DAGNode> Parser::parseExpr() {

		// const | func
		if (*bufptr != '(') {
			//const | func

			size_t expr_ln = line_number;
			std::string s = getSymbol();

			std::shared_ptr<DAGNode> expr = parseConstFunc(s);
			if(expr->isErr()) err_unkwn_sym(s, expr_ln);
			return expr;
		}

		// (<identifier> <expr>+)
		// ((_ f args) <expr>+)
		parseLpar();
		std::shared_ptr<DAGNode> expr = nullptr;
		size_t expr_ln = line_number;
		if(*bufptr == '('){
			parseLpar();
			// ((_ f args) <expr>+)
			std::string s = getSymbol();
			if(s == "_"){
				// (_ f args): a function with parameters
				// ((_ f args) param) 
				std::string f = getSymbol();
				std::vector<std::shared_ptr<DAGNode>> args = parseParams();
				parseRpar();
				std::vector<std::shared_ptr<DAGNode>> params = parseParams();
				expr = parseParamFunc(f, args, params);
			}
			if(!expr || expr->isErr()) err_unkwn_sym(s, expr_ln);
		}
		else{
			// (<identifier> <expr>+)
			std::string s = getSymbol();

			//parse identifier and get params
			if(s == "_"){
				// ( _ <identifier> <expr>+)
				//     ^
				std::string s = getSymbol();
				if(s[0] == 'b' && s[1] == 'v'){
					// e.g. (_ bv13 32)
					std::string num = s.substr(2);
					std::string width_ = getSymbol();
					size_t width = std::stoi(width_);
					expr = mkConstBv(num, width);
				}
			}
			else if (s == "let") {
				expr = parseLet();
				if (expr->isErr())
					err_all(expr, "let", expr_ln);
			}
			else {
				std::vector<std::shared_ptr<DAGNode>> params = parseParams();
				expr = parseOper(s, params);

				// check error
				if (expr->isErr()) err_all(expr, s, expr_ln);
			}
		}
		parseRpar();

		return expr;
	}

	
	std::shared_ptr<DAGNode> Parser::parseConstFunc(const std::string& s){
		// these have the highest priority
		if(let_key_map.find(s) != let_key_map.end()){
			return let_key_map[s];
		}
		else if(fun_key_map.find(s) != fun_key_map.end()){
			// function name
			return fun_key_map[s];
		}
		else if(fun_var_map.find(s) != fun_var_map.end()){
			// function variable name
			return fun_var_map[s];
		}
		else if(var_names.find(s) != var_names.end()){
			// variable name
			return node_list[var_names[s]];
		}
		// following Common Lisp's conventions, enclosing
		// a simple symbol in vertical bars does not produce a new symbol.
		else if(s.size() > 1 && 
				s[0] == '|'  && 
				s[s.size() - 1] == '|' &&
				var_names.find(s.substr(1, s.size() - 2)) != var_names.end()){
			// string
			return node_list[var_names[s.substr(1, s.size() - 2)]];
		}
		// otherwise, it is a constant
		else if(s == "pi"){
			return mkPi();
		}
		else if(s == "e"){
			return mkE();
		}
		else if(s == "inf"){
			return mkInfinity(options->isIntTheory()? INT_SORT : REAL_SORT);
		}
		else if(s == "+inf"){
			return mkPosInfinity(options->isIntTheory()? INT_SORT : REAL_SORT);
		}
		else if(s == "-inf"){
			return mkNegInfinity(options->isIntTheory()? INT_SORT : REAL_SORT);
		}
		else if(s == "epsion"){
			return mkEpsilon();
		}
		else if(s == "+epsilon"){
			return mkPosEpsilon();
		}
		else if(s == "-epsilon"){
			return mkNegEpsilon();
		}
		else if(s == "NaN"){
			return mkNan();
		}
		// support -3 (before only - 3)
		else if(isIntUtil(s)){
			// additional process -> constant can be real or integer
			// 0 -> Int or Real?
			return mkConstInt(s);
		}
		else if(isRealUtil(s)){
			return mkConstReal(s);
		}
		else if(isScientificNotationUtil(s)){
			// 解析科学计数法并转换为普通实数
			std::string parsed = parseScientificNotation(s);
			return mkConstReal(parsed);
		}
		else if(isBVUtil(s)){
			return mkConstBv(s, s.size() - 2);
		}
		// else if(isFPUtil(s)){
		// 	return mkConstFP(s);
		// }
		else if(isStrUtil(s)){
			return mkConstStr(s);
		}
		else if (s == "true") {
			return mkTrue();
		}
		else if (s == "false") {
			return mkFalse();
		}
		// no parameters
		else if (s == "re.none"){
			return mkRegNone();
		}
		else if (s == "re.all"){
			return mkRegAll();
		}
		else if (s == "re.allchar"){
			return mkRegAllChar();
		}
		else {
			return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
		}
	}

	std::shared_ptr<DAGNode> Parser::parseParamFunc(const std::string& f, const std::vector<std::shared_ptr<DAGNode>> &args, const std::vector<std::shared_ptr<DAGNode>> &params){
		if (f == "extract") {
			cassert(args.size() == 2, "Invalid number of arguments for extract");
			cassert(params.size() == 1, "Invalid number of parameters for extract");
			return mkBvExtract(params[0], args[0], args[1]);
		}
		else if (f == "repeat") {
			cassert(args.size() == 1, "Invalid number of arguments for repeat");
			cassert(params.size() == 1, "Invalid number of parameters for repeat");
			return mkBvRepeat(params[0], args[0]);
		}
		else if (f == "zero_extend") {
			cassert(args.size() == 1, "Invalid number of arguments for zero_extend");
			cassert(params.size() == 1, "Invalid number of parameters for zero_extend");
			return mkBvZeroExt(params[0], args[0]);
		}
		else if (f == "sign_extend") {
			cassert(args.size() == 1, "Invalid number of arguments for sign_extend");
			cassert(params.size() == 1, "Invalid number of parameters for sign_extend");
			return mkBvSignExt(params[0], args[0]);
		}
		else if(f == "int_to_bv") {
			cassert(args.size() == 1, "Invalid number of arguments for int_to_bv");
			cassert(params.size() == 1, "Invalid number of parameters for int_to_bv");
			return mkIntToBv(params[0], args[0]);
		}
		else if(f == "rotate_left") {
			cassert(args.size() == 1, "Invalid number of arguments for rotate_left");
			cassert(params.size() == 1, "Invalid number of parameters for rotate_left");
			return mkBvRotateLeft(params[0], args[0]);
		}
		else if(f == "rotate_right"){
			cassert(args.size() == 1, "Invalid number of arguments for rotate_right");
			cassert(params.size() == 1, "Invalid number of parameters for rotate_right");
			return mkBvRotateRight(params[0], args[0]);
		}
		else if (f == "re.loop") {
			cassert(params.size() == 1, "Invalid number of parameters for re.loop");
			cassert(args.size() == 2, "Invalid number of arguments for re.loop");
			return mkRegLoop(params[0], args[0], args[1]);
		}
		else return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
	}

	std::shared_ptr<DAGNode> Parser::parseOper(const std::string& s, const std::vector<std::shared_ptr<DAGNode>> &params){
		if (s == "and") {
			return mkAnd(params);
		}
		else if (s == "or") {
			return mkOr(params);
		}
		else if (s == "not") {
			cassert(params.size() == 1, "Invalid number of parameters for not");
			return mkNot(params[0]);
		}
		else if (s == "=>") {
			return mkImplies(params);
		}
		else if (s == "xor") {
			return mkXor(params);
		}
		else if (s == "=" || s == "==" || s == "<->" || s == "iff" || s == "<=>") {
			return mkEq(params);
		}
		else if (s == "distinct" || s == "!=" || s == "<>") {
			return mkDistinct(params);
		}
		else if (s == "ite") {
			return mkIte(params);
		}
		else if (s == "+") {
			return mkAdd(params);
		}
		else if (s == "-") {
			return mkSub(params);
		}
		else if (s == "*") {
			return mkMul(params);
		}
		else if (s == "iand") {
			return mkIand(params);
		}
		else if (s == "pow2") {
			cassert(params.size() == 1, "Invalid number of parameters for pow2");
			return mkPow2(params[0]);
		}
		else if (s == "pow" || s == "**" || s == "^") {
			cassert(params.size() == 2, "Invalid number of parameters for pow");
			return mkPow(params[0], params[1]);
		}
		else if (s == "div") {
			cassert(params.size() == 2, "Invalid number of parameters for div");
			return mkDivInt(params[0], params[1]);
		}
		else if (s == "/") {
			cassert(params.size() == 2, "Invalid number of parameters for div");
			return mkDivReal(params[0], params[1]);
		}
		else if (s == "mod") {
			cassert(params.size() == 2, "Invalid number of parameters for mod");
			return mkMod(params[0], params[1]);
		}
		else if (s == "abs") {
			cassert(params.size() == 1, "Invalid number of parameters for abs");
			return mkAbs(params[0]);
		}
		else if (s == "sqrt") {
			cassert(params.size() == 1, "Invalid number of parameters for sqrt");
			return mkSqrt(params[0]);
		}
		else if (s == "safesqrt") {
			cassert(params.size() == 1, "Invalid number of parameters for safesqrt");
			return mkSafeSqrt(params[0]);
		}
		else if (s == "ceil") {
			cassert(params.size() == 1, "Invalid number of parameters for ceil");
			return mkCeil(params[0]);
		}
		else if (s == "floor") {
			cassert(params.size() == 1, "Invalid number of parameters for floor");
			return mkFloor(params[0]);
		}
		else if (s == "round") {
			cassert(params.size() == 1, "Invalid number of parameters for round");
			return mkRound(params[0]);
		}
		else if (s == "exp") {
			cassert(params.size() == 1, "Invalid number of parameters for exp");
			return mkExp(params[0]);
		}
		else if (s == "ln" || s == "loge") {
			cassert(params.size() == 1, "Invalid number of parameters for ln");
			return mkLn(params[0]);
		}
		else if (s == "lg" || s == "log10"){
			cassert(params.size() == 1, "Invalid number of parameters for lg");
			return mkLg(params[0]);
		}
		else if (s == "lb" || s == "log2"){
			cassert(params.size() == 1, "Invalid number of parameters for lb");
			return mkLb(params[0]);
		}
		else if (s == "log") {
			if(params.size() == 1){
				// ln(param)
				return mkLn(params[0]);
			}
			else if(params.size() == 2){
				// log(param1, param2)
				return mkLog(params[0], params[1]);
			}
			else err_param_mis("log", line_number);
		}
		else if (s == "sin") {
			cassert(params.size() == 1, "Invalid number of parameters for sin");
			return mkSin(params[0]);
		}
		else if (s == "cos") {
			cassert(params.size() == 1, "Invalid number of parameters for cos");
			return mkCos(params[0]);
		}
		else if (s == "tan") {
			cassert(params.size() == 1, "Invalid number of parameters for tan");
			return mkTan(params[0]);
		}
		else if (s == "asin" || s == "arcsin") {
			cassert(params.size() == 1, "Invalid number of parameters for asin");
			return mkAsin(params[0]);
		}
		else if (s == "acos" || s == "arccos") {
			cassert(params.size() == 1, "Invalid number of parameters for acos");
			return mkAcos(params[0]);
		}
		else if (s == "atan" || s == "arctan") {
			cassert(params.size() == 1, "Invalid number of parameters for atan");
			return mkAtan(params[0]);
		}
		else if (s == "sinh") {
			cassert(params.size() == 1, "Invalid number of parameters for sinh");
			return mkSinh(params[0]);
		}
		else if (s == "cosh") {
			cassert(params.size() == 1, "Invalid number of parameters for cosh");
			return mkCosh(params[0]);
		}
		else if (s == "tanh") {
			cassert(params.size() == 1, "Invalid number of parameters for tanh");
			return mkTanh(params[0]);
		}
		else if (s == "asinh" || s == "arcsinh") {
			cassert(params.size() == 1, "Invalid number of parameters for asinh");
			return mkAsinh(params[0]);
		}
		else if (s == "acosh" || s == "arccosh") {
			cassert(params.size() == 1, "Invalid number of parameters for acosh");
			return mkAcosh(params[0]);
		}
		else if (s == "atanh" || s == "arctanh") {
			cassert(params.size() == 1, "Invalid number of parameters for atanh");
			return mkAtanh(params[0]);
		}
		else if (s == "asech" || s == "arcsec") {
			cassert(params.size() == 1, "Invalid number of parameters for asech");
			return mkAsech(params[0]);
		}
		else if (s == "acsch" || s == "arccsch") {
			cassert(params.size() == 1, "Invalid number of parameters for acsch");
			return mkAcsch(params[0]);
		}
		else if (s == "acoth" || s == "arccoth") {
			cassert(params.size() == 1, "Invalid number of parameters for acoth");
			return mkAcoth(params[0]);
		}
		else if (s == "atan2" || s == "arctan2") {
			cassert(params.size() == 2, "Invalid number of parameters for atan2");
			return mkAtan2(params[0], params[1]);
		}
		else if (s == "<=") {
			cassert(params.size() == 2, "Invalid number of parameters for <= ");
			return mkLe(params[0], params[1]);
		}
		else if (s == "<") {
			cassert(params.size() == 2, "Invalid number of parameters for <");
			return mkLt(params[0], params[1]);
		}
		else if (s == ">=") {
			cassert(params.size() == 2, "Invalid number of parameters for >= ");
			return mkGe(params[0], params[1]);
		}
		else if (s == ">") {
			cassert(params.size() == 2, "Invalid number of parameters for >");
			return mkGt(params[0], params[1]);
		}
		else if (s == "to_real") {
			cassert(params.size() == 1, "Invalid number of parameters for to_real");
			return mkToReal(params[0]);
		}
		else if (s == "to_int") {
			cassert(params.size() == 1, "Invalid number of parameters for to_int");
			return mkToInt(params[0]);
		}
		else if (s == "is_int") {
			cassert(params.size() == 1, "Invalid number of parameters for is_int");
			return mkIsInt(params[0]);
		}
		else if (s == "is_divisible") {
			cassert(params.size() == 2, "Invalid number of parameters for is_divisible");
			return mkIsDivisible(params[0], params[1]);
		}
		else if (s == "is_prime") {
			cassert(params.size() == 1, "Invalid number of parameters for is_prime");
			return mkIsPrime(params[0]);
		}
		else if (s == "is_even") {
			cassert(params.size() == 1, "Invalid number of parameters for is_even");
			return mkIsEven(params[0]);
		}
		else if (s == "is_odd") {
			cassert(params.size() == 1, "Invalid number of parameters for is_odd");
			return mkIsOdd(params[0]);
		}
		else if (s == "gcd") {
			cassert(params.size() == 2, "Invalid number of parameters for gcd");
			return mkGcd(params[0], params[1]);
		}
		else if (s == "lcm") {
			cassert(params.size() == 2, "Invalid number of parameters for lcm");
			return mkLcm(params[0], params[1]);
		}
		else if (s == "factorial") {
			cassert(params.size() == 1, "Invalid number of parameters for factorial");
			return mkFact(params[0]);
		}
		else if (s == "bvnot") {
			cassert(params.size() == 1, "Invalid number of parameters for bvnot");
			return mkBvNot(params[0]);
		}
		else if (s == "bvneg") {
			cassert(params.size() == 1, "Invalid number of parameters for bvneg");
			return mkBvNeg(params[0]);
		}
		else if (s == "bvand") {
			return mkBvAnd(params);
		}
		else if (s == "bvor") {
			return mkBvOr(params);
		}
		else if (s == "bvxor") {
			return mkBvXor(params);
		}
		else if (s == "bvnand") {
			return mkBvNand(params);
		}
		else if (s == "bvnor") {
			return mkBvNor(params);
		}
		else if (s == "bvxnor") {
			return mkBvXnor(params);
		}
		else if (s == "bvcomp") {
			cassert(params.size() == 2, "Invalid number of parameters for bvcomp");
			return mkBvComp(params[0], params[1]);
		}
		else if (s == "bvadd") {
			return mkBvAdd(params);
		}
		else if (s == "bvsub") {
			return mkBvSub(params);
		}
		else if (s == "bvmul") {
			return mkBvMul(params);
		}
		else if (s == "bvudiv") {
			cassert(params.size() == 2, "Invalid number of parameters for bvudiv");
			return mkBvUdiv(params[0], params[1]);
		}
		else if (s == "bvurem") {
			cassert(params.size() == 2, "Invalid number of parameters for bvurem");
			return mkBvUrem(params[0], params[1]);
		}
		else if (s == "bvsdiv") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsdiv");
			return mkBvSdiv(params[0], params[1]);
		}
		else if (s == "bvsrem") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsrem");
			return mkBvSrem(params[0], params[1]);
		}
		else if (s == "bvsmod") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsmod");
			return mkBvSmod(params[0], params[1]);
		}
		else if (s == "bvshl") {
			cassert(params.size() == 2, "Invalid number of parameters for bvshl");
			return mkBvShl(params[0], params[1]);
		}
		else if (s == "bvlshr") {
			cassert(params.size() == 2, "Invalid number of parameters for bvlshr");
			return mkBvLshr(params[0], params[1]);
		}
		else if (s == "bvashr") {
			cassert(params.size() == 2, "Invalid number of parameters for bvashr");
			return mkBvAshr(params[0], params[1]);
		}
		else if (s == "bvult") {
			cassert(params.size() == 2, "Invalid number of parameters for bvult");
			return mkBvUlt(params[0], params[1]);
		}
		else if (s == "bvule") {
			cassert(params.size() == 2, "Invalid number of parameters for bvule");
			return mkBvUle(params[0], params[1]);
		}
		else if (s == "bvugt") {
			cassert(params.size() == 2, "Invalid number of parameters for bvugt");
			return mkBvUgt(params[0], params[1]);
		}
		else if (s == "bvuge") {
			cassert(params.size() == 2, "Invalid number of parameters for bvuge");
			return mkBvUge(params[0], params[1]);
		}
		else if (s == "bvslt") {
			cassert(params.size() == 2, "Invalid number of parameters for bvslt");
			return mkBvSlt(params[0], params[1]);
		}
		else if (s == "bvsle") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsle");
			return mkBvSle(params[0], params[1]);
		}
		else if (s == "bvsgt") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsgt");
			return mkBvSgt(params[0], params[1]);
		}
		else if (s == "bvsge") {
			cassert(params.size() == 2, "Invalid number of parameters for bvsge");
			return mkBvSge(params[0], params[1]);
		}
		else if (s == "concat") {
			return mkBvConcat(params);
		}
		else if (s == "bv2nat") {
			cassert(params.size() == 1, "Invalid number of parameters for bv2nat");
			return mkBvToNat(params[0]);
		}
		else if (s == "nat2bv") {
			cassert(params.size() == 2, "Invalid number of parameters for nat2bv");
			return mkNatToBv(params[0], params[1]);
		}
		else if (s == "int2bv") {
			cassert(params.size() == 2, "Invalid number of parameters for int2bv");
			return mkIntToBv(params[0], params[1]);
		}
		else if (s == "bv2int") {
			cassert(params.size() == 1, "Invalid number of parameters for bv2int");
			return mkBvToInt(params[0]);
		}
		else if (s == "fp.abs") {
			cassert(params.size() == 1, "Invalid number of parameters for fp.abs");
			return mkFpAbs(params[0]);
		}
		else if (s == "fp.neg") {
			cassert(params.size() == 1, "Invalid number of parameters for fp.neg");
			return mkFpNeg(params[0]);
		}
		else if (s == "fp.add") {
			return mkFpAdd(params);
		}
		else if (s == "fp.sub") {
			return mkFpSub(params);
		}
		else if (s == "fp.mul") {
			return mkFpMul(params);
		}
		else if (s == "fp.div") {
			return mkFpDiv(params);
		}
		else if (s == "fp.fma") {
			cassert(params.size() == 3, "Invalid number of parameters for fp.fma");
			return mkFpFma(params);
		}
		else if (s == "fp.sqrt") {
			cassert(params.size() == 1, "Invalid number of parameters for fp.sqrt");
			return mkFpSqrt(params[0]);
		}
		else if (s == "fp.rem") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.rem");
			return mkFpRem(params[0], params[1]);
		}
		else if (s == "fp.roundToIntegral") {
			cassert(params.size() == 1, "Invalid number of parameters for fp.roundToIntegral");
			return mkFpRoundToIntegral(params[0]);
		}
		else if (s == "fp.min") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.min");
			return mkFpMin(params);
		}
		else if (s == "fp.max") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.max");
			return mkFpMax(params);
		}
		else if (s == "fp.leq") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.leq");
			return mkFpLe(params[0], params[1]);
		}
		else if (s == "fp.lt") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.lt");
			return mkFpLt(params[0], params[1]);
		}
		else if (s == "fp.geq") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.geq");
			return mkFpGe(params[0], params[1]);
		}
		else if (s == "fp.gt") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.gt");
			return mkFpGt(params[0], params[1]);
		}
		else if (s == "fp.eq" || s == "fp.=" || s == "fp.==") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.eq");
			return mkFpEq(params[0], params[1]);
		}
		else if (s == "fp.ne" || s == "fp.!=" || s == "fp.neq") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.ne");
			return mkFpNe(params[0], params[1]);
		}
		else if (s == "fp.to_ubv") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.to_ubv");
			return mkFpToUbv(params[0], params[1]);
		}
		else if (s == "fp.to_sbv") {
			cassert(params.size() == 2, "Invalid number of parameters for fp.to_sbv");
			return mkFpToSbv(params[0], params[1]);
		}
		else if (s == "fp.to_real") {
			cassert(params.size() == 1, "Invalid number of parameters for fp.to_real");
			return mkFpToReal(params[0]);
		}
		else if (s == "to_fp") {
			cassert(params.size() == 3, "Invalid number of parameters for to_fp");
			return mkToFp(params[0], params[1], params[2]);
		}
		else if (s == "fp.isNormal"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isNormal");
			return mkFpIsNormal(params[0]);
		}
		else if (s == "fp.isSubnormal"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isSubnormal");
			return mkFpIsSubnormal(params[0]);
		}
		else if (s == "fp.isZero"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isZero");
			return mkFpIsZero(params[0]);
		}
		else if (s == "fp.isInfinite"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isInfinite");
			return mkFpIsInf(params[0]);
		}
		else if (s == "fp.isNaN"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isNaN");
			return mkFpIsNan(params[0]);
		}
		else if (s == "fp.isNegative"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isNegative");
			return mkFpIsNeg(params[0]);
		}
		else if (s == "fp.isPositive"){
			cassert(params.size() == 1, "Invalid number of parameters for fp.isPositive");
			return mkFpIsPos(params[0]);
		}
		else if (s == "select") {
			cassert(params.size() == 2, "Invalid number of parameters for select");
			return mkSelect(params[0], params[1]);
		}
		else if (s == "store") {
			cassert(params.size() == 3, "Invalid number of parameters for store");
			return mkStore(params[0], params[1], params[2]);
		}
		else if (s == "str.len") {
			cassert(params.size() == 1, "Invalid number of parameters for str.len");
			return mkStrLen(params[0]);
		}
		else if (s == "str.++") {
			return mkStrConcat(params);
		}
		else if (s == "str.substr") {
			cassert(params.size() == 3, "Invalid number of parameters for str.substr");
			return mkStrSubstr(params[0], params[1], params[2]);
		}
		else if (s == "str.prefixof") {
			cassert(params.size() == 2, "Invalid number of parameters for str.prefixof");
			return mkStrPrefixof(params[0], params[1]);
		}
		else if (s == "str.suffixof") {
			cassert(params.size() == 2, "Invalid number of parameters for str.suffixof");
			return mkStrSuffixof(params[0], params[1]);
		}
		else if (s == "str.indexof") {
			cassert(params.size() == 3, "Invalid number of parameters for str.indexof");
			return mkStrIndexof(params[0], params[1], params[2]);
		}
		else if (s == "str.at") {
			cassert(params.size() == 2, "Invalid number of parameters for str.at");
			return mkStrCharat(params[0], params[1]);
		}
		else if (s == "str.update") {
			cassert(params.size() == 3, "Invalid number of parameters for str.update");
			return mkStrUpdate(params[0], params[1], params[2]);
		}
		else if (s == "str.replace") {
			cassert(params.size() == 3, "Invalid number of parameters for str.replace");
			return mkStrReplace(params[0], params[1], params[2]);
		}
		else if (s == "str.replace_all") {
			cassert(params.size() == 3, "Invalid number of parameters for str.replace_all");
			return mkStrReplaceAll(params[0], params[1], params[2]);
		}
		else if (s == "str.replace_re") {
			cassert(params.size() == 3, "Invalid number of parameters for str.replace_re");
			return mkReplaceReg(params[0], params[1], params[2]);
		}
		else if (s == "str.replace_all_re") {
			cassert(params.size() == 3, "Invalid number of parameters for str.replace_all_re");
			return mkReplaceRegAll(params[0], params[1], params[2]);
		}
		else if (s == "str.to_lower") {
			cassert(params.size() == 1, "Invalid number of parameters for str.to_lower");
			return mkStrToLower(params[0]);
		}
		else if (s == "str.to_upper") {
			cassert(params.size() == 1, "Invalid number of parameters for str.to_upper");
			return mkStrToUpper(params[0]);
		}
		else if (s == "str.rev") {
			cassert(params.size() == 1, "Invalid number of parameters for str.rev");
			return mkStrRev(params[0]);
		}
		else if (s == "str.split") {
			cassert(params.size() == 2, "Invalid number of parameters for str.split");
			return mkStrSplit(params[0], params[1]);
		}
		else if (s == "str.split_at") {
			cassert(params.size() == 3, "Invalid number of parameters for str.split_at");
			return mkStrSplitAt(params[0], params[1], params[2]);
		}
		else if (s == "str.num_splits") {
			cassert(params.size() == 2, "Invalid number of parameters for str.num_splits");
			return mkStrNumSplits(params[0], params[1]);
		}
		else if (s == "str.<"){
			cassert(params.size() == 2, "Invalid number of parameters for str.<");
			return mkStrLt(params[0], params[1]);
		}
		else if (s == "str.<="){
			cassert(params.size() == 2, "Invalid number of parameters for str.<=");
			return mkStrLe(params[0], params[1]);
		}
		else if (s == "str.>"){
			cassert(params.size() == 2, "Invalid number of parameters for str.>");
			return mkStrGt(params[0], params[1]);
		}
		else if (s == "str.>="){
			cassert(params.size() == 2, "Invalid number of parameters for str.>=");
			return mkStrGe(params[0], params[1]);
		}
		else if (s == "str.in_re"){
			cassert(params.size() == 2, "Invalid number of parameters for str.in_re");
			return mkStrInReg(params[0], params[1]);
		}
		else if (s == "str.contains"){
			cassert(params.size() == 2, "Invalid number of parameters for str.contains");
			return mkStrContains(params[0], params[1]);
		}
		else if (s == "str.is_digit"){
			cassert(params.size() == 1, "Invalid number of parameters for str.is_digit");
			return mkStrIsDigit(params[0]);
		}
		else if (s == "str.from_int"){
			cassert(params.size() == 1, "Invalid number of parameters for str.from_int");
			return mkStrFromInt(params[0]);
		}
		else if (s == "str.to_int"){
			cassert(params.size() == 1, "Invalid number of parameters for str.to_int");
			return mkStrToInt(params[0]);
		}
		else if (s == "str.to_re"){
			cassert(params.size() == 1, "Invalid number of parameters for str.to_re");
			return mkStrToReg(params[0]);
		}
		else if (s == "str.to_code"){
			cassert(params.size() == 1, "Invalid number of parameters for str.to_code");
			return mkStrToCode(params[0]);
		}
		else if (s == "str.from_code"){
			cassert(params.size() == 1, "Invalid number of parameters for str.from_code");
			return mkStrFromCode(params[0]);
		}
		else if (s == "re.++") {
			return mkRegConcat(params);
		}
		else if (s == "re.union") {
			return mkRegUnion(params);
		}
		else if (s == "re.inter") {
			return mkRegInter(params);
		}
		else if (s == "re.diff") {
			return mkRegDiff(params);
		}
		else if (s == "re.*") {
			cassert(params.size() == 1, "Invalid number of parameters for re.*");
			return mkRegStar(params[0]);
		}
		else if (s == "re.+") {
			cassert(params.size() == 1, "Invalid number of parameters for re.+");
			return mkRegPlus(params[0]);
		}
		else if (s == "re.?" || s == "re.opt") {
			cassert(params.size() == 1, "Invalid number of parameters for re.?");
			return mkRegOpt(params[0]);
		}
		else if (s == "re.range") {
			cassert(params.size() == 2, "Invalid number of parameters for re.range");
			return mkRegRange(params[0], params[1]);
		}
		else if (s == "re.repeat") {
			cassert(params.size() == 2, "Invalid number of parameters for re.repeat");
			return mkRegRepeat(params[0], params[1]);
		}
		else if (s == "re.comp") {
			cassert(params.size() == 1, "Invalid number of parameters for re.comp");
			return mkRegComplement(params[0]);
		}
		else if (fun_key_map.find(s) != fun_key_map.end()) {
			// function
			return applyFun(fun_key_map[s], params);
		}
		
		return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
	}

	// sort ::= <identifier> | (<identifier> <sort>+)
	std::shared_ptr<Sort> Parser::parseSort(){
		if (*bufptr != '(') {
			// <identifier>
			size_t expr_ln = line_number;
			std::string s = getSymbol();

			if(s == "Bool"){
				return BOOL_SORT;
			}
			else if(s == "Int"){
				return INT_SORT;
			}
			else if(s == "Real"){
				return REAL_SORT;
			}
			else if(s == "String"){
				return STR_SORT;
			}
			else err_unkwn_sym(s, expr_ln);
		}
		// (<identifier> <sort>+)
		// (_ <identifier> <param>+)
		parseLpar();
		size_t expr_ln = line_number;
		std::string s = getSymbol();

		//parse identifier and get params
		std::shared_ptr<Sort> sort = NULL_SORT;
		if (s == "Array") {
			// (Array S T)
			// S: sort of index
			// T: sort of value        
			std::shared_ptr<Sort> sortS = parseSort();
			std::shared_ptr<Sort> sortT = parseSort();
			std::string sort_key_name = "ARRAY_" + sortS->toString() + "_" + sortT->toString();
			if(sort_key_map.find(sort_key_name) != sort_key_map.end()){
				sort = sort_key_map[sort_key_name];
			}
			else{
				sort = mkArraySort(sortS, sortT);
				sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
			}
		}
		else if(s == "Datatype"){}
		else if(s == "Set"){}
		else if(s == "Relation"){}
		else if(s == "Bag"){}
		else if(s == "Sequence"){}
		else if(s == "UF"){
			// // (UF S T)
			// // S: sort of parameters
			// // T: sort of return value
			// SortS = parseSort();
			// SortT = parseSort();
			// return std::make_shared<Sort>(SORT_KIND::SK_UF, "UF", 2, {sortS, sortT});
		}
		else if(s == "_"){
			// (_ <identifier> <param>+)
			std::string id = getSymbol();

			if(id == "BitVec"){
				// (_ BitVec n)
				// n: bit-width
				std::string n = getSymbol();
				std::string sort_key_name = "BV_" + n;
				if(sort_key_map.find(sort_key_name) != sort_key_map.end()){
					sort = sort_key_map[sort_key_name];
				}
				else{
					sort = mkBVSort(std::stoi(n));
					sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
				}
			}
			else if(id == "FloatingPoint"){
				// (_ FloatingPoint e s)
				// e: exponent width
				// s: significand width
				std::string e = getSymbol();
				std::string s = getSymbol();
				std::string sort_key_name = "FP_" + e + "_" + s;
				if(sort_key_map.find(sort_key_name) != sort_key_map.end()){
					sort = sort_key_map[sort_key_name];
				}
				else{
					sort = mkFPSort(std::stoi(e), std::stoi(s));
					sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
				}
			}
			else err_unkwn_sym(s, expr_ln);
		}
		else err_unkwn_sym(s, expr_ln);
		parseRpar();

		return sort;
	}

	std::vector<std::shared_ptr<DAGNode>> Parser::parseParams() {

		std::vector<std::shared_ptr<DAGNode>> params;

		while (*bufptr != ')'){
			params.emplace_back(parseExpr());
		}

		return params;

	}

	// struct for let context
	struct LetContext {
		std::vector<std::shared_ptr<DAGNode>> params;
		std::vector<std::string> key_list;
		int nesting_level;
		bool is_complete;
		
		LetContext(int level = 0) : nesting_level(level), is_complete(false) {}
	};
	/*
	keybinding ::= (<symbol> expr)
	(let (<keybinding>+) expr), return expr
	*/
	std::shared_ptr<DAGNode> Parser::parseLet() {
		// This function uses an iterative approach instead of recursion to handle nested let expressions
		
		// Create a stack to store parsing states and contexts
		std::vector<LetContext> stateStack;
		
		// Push initial state onto the stack
		stateStack.emplace_back(LetContext(0));
		
		// Enter the initial "("
		parseLpar();
		
		// Main loop to handle all nested let expressions
		while (!stateStack.empty()) {
			auto &currentState = stateStack.back();
			auto &params = currentState.params;
			auto &key_list = currentState.key_list;
			
			if(!currentState.is_complete){
				// Parse the current let bindings
				while (*bufptr != ')') {
					// Process binding expression (<symbol> expr)
					parseLpar();
					
					size_t name_ln = line_number;
					std::string name = getSymbol();
					
					// Check for duplicate key bindings
					if (let_key_map.find(name) != let_key_map.end()) {
						// Clean up all variable bindings in the state stack
						for (auto &state : stateStack) {
							for (const auto &key : state.key_list) {
								let_key_map.erase(key);
							}
						}
						return mkErr(ERROR_TYPE::ERR_MUL_DECL);
					}
					
					// Parse the expression value (this won't trigger recursive let parsing)
					std::shared_ptr<DAGNode> expr = parseExpr();
					
					if (expr->isErr()) {
						// Clean up all variable bindings in the state stack
						for (auto &state : stateStack) {
							for (const auto &key : state.key_list) {
								let_key_map.erase(key);
							}
						}
						err_all(expr, name, name_ln);
					}
					
					// Add the binding
					let_key_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, expr));
					params.emplace_back(expr);
					key_list.emplace_back(name);
					
					parseRpar();
				}
				
				// Finished parsing all bindings for the current let, handle the closing parenthesis
				parseRpar();
			}
			
			// Process the body of the let expression
			if (*bufptr == '(' && peekSymbol() == "let") {
				// If the body is another let expression, we don't recursively call parseLet
				// Instead, push it as a new state onto the stack
				parseLpar();  // Consume '('
				std::string let_key = getSymbol();  // Consume "let"
				cassert(let_key == "let", "Invalid keyword for let");
				parseLpar();  // Consume the second let expression's starting '('
				
				stateStack.emplace_back(LetContext(currentState.nesting_level + 1));
			}
			else{
				if(*bufptr != ')'){
					std::shared_ptr<DAGNode> expr = parseExpr();
					params.insert(params.begin(), expr);
				}
				std::shared_ptr<DAGNode> res = mkOper(params[0]->getSort(), NODE_KIND::NT_LET, params);

				// Remove all variable bindings for the current state
				for (const auto &key : key_list) {
					let_key_map.erase(key);
				}

				// State processing complete, pop from stack
				stateStack.pop_back();

				// If stack is empty, return the result; otherwise, use the result as the body of the parent let
				if (stateStack.empty()) {
					return res;
				}
				else{
					// Consume the closing parenthesis
					parseRpar();
					// Use the result as the body of the parent let
					stateStack.back().params.insert(stateStack.back().params.begin(), res);
					stateStack.back().is_complete = true;
				}
			}
		}
		
		// Should not reach here, but added for safety
		return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
	}

	// Helper function to preview the next symbol without consuming input
	std::string Parser::peekSymbol() {
		char *save_bufptr = bufptr;
		SCAN_MODE save_mode = scan_mode;
		size_t save_line = line_number;
		
		std::string symbol;
		if (*bufptr == '(') {
			bufptr++;
			scanToNextSymbol();
			symbol = getSymbol();
		} else {
			symbol = getSymbol();
		}
		
		// Restore state
		bufptr = save_bufptr;
		scan_mode = save_mode;
		line_number = save_line;
		
		return symbol;
	}

	std::shared_ptr<DAGNode> Parser::applyFun(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> & params){
		// check the number of params
		if (fun->getFuncParamsSize() != params.size()){
			return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
		}

		// For declare-fun (uninterpreted functions), create a function application node
		if(fun->getFuncBody()->isNull()){
			// Create a function application node with proper structure
			std::shared_ptr<DAGNode> result = std::make_shared<DAGNode>(fun->getSort(), NODE_KIND::NT_APPLY_UF, fun->getName(), params);
			return result;
		}

		if(fun->getFuncBody()->isErr()){
			return fun->getFuncBody();
		}
		
		// variable map for local variables
		boost::unordered_map<std::string, std::shared_ptr<DAGNode>> new_params_map;
		std::vector<std::shared_ptr<DAGNode>> func_params = fun->getFuncParams();
		for (size_t i = 0; i < func_params.size(); i++) {
			if(params[i]->isErr()){
				return params[i];
			}
			new_params_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(func_params[i]->getName(), params[i]));
		}
		
		// function content
		std::shared_ptr<DAGNode> formula = fun->getFuncBody();

		// Iterative implementation to replace recursive applyFunPostOrder
		return applyFunPostOrder(formula, new_params_map);
	}

	// Iterative version of post-order traversal function application
	std::shared_ptr<DAGNode> Parser::applyFunPostOrder(std::shared_ptr<DAGNode> node, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> & params){
		if (!node) return nullptr;
		
		// Stack to track nodes to process
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		
		// Map to store processed results for each node
		boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> results;
		
		// Push initial node to stack
		todo.push(std::make_pair(node, false));
		
		while (!todo.empty()) {
			std::shared_ptr<DAGNode> current = todo.top().first;
			bool processed = todo.top().second;
			todo.pop();
			
			if (processed) {
				// Node is being revisited after processing its children
				std::vector<std::shared_ptr<DAGNode>> childResults;
				
				// Collect results from all children
				for (size_t i = 0; i < current->getChildrenSize(); i++) {
					childResults.emplace_back(results[current->getChild(i)]);
				}
				
				// Create a new node with processed children
				std::shared_ptr<DAGNode> result = mkOper(current->getSort(), current->getKind(), childResults);
				results[current] = result;
			} else {
				// First visit to this node
				if (current->isFuncParam()) {
					// Function parameter - replace with actual parameter
					auto it = params.find(current->getName());
					if (it != params.end()) {
						results[current] = it->second;
					} else {
						// Parameter not found, this should not happen if applyFun is called correctly
						results[current] = mkErr(ERROR_TYPE::ERR_FUN_LOCAL_VAR);
					}
				} else if (current->isConst()) {
					// Constants remain unchanged
					results[current] = current;
				} else if (current->isFuncApply()) {
					// Function application node
					std::vector<std::shared_ptr<DAGNode>> funcParams;
					
					// First, mark the node for revisit after processing children
					todo.push(std::make_pair(current, true));
					
					// Process the function body and parameters
					for (size_t i = 1; i < current->getChildrenSize(); i++) {
						todo.push(std::make_pair(current->getChild(i), false));
						funcParams.emplace_back(current->getChild(i));
					}
					
					// Apply the function to its parameters
					results[current] = applyFun(current->getFuncBody(), funcParams);
				} else {
					// Operator node - process all children first
					todo.push(std::make_pair(current, true));
					
					// Push all children onto the stack in reverse order
					for (int i = current->getChildrenSize() - 1; i >= 0; i--) {
						todo.push(std::make_pair(current->getChild(i), false));
					}
				}
			}
		}
		
		return results[node];
	}
	
	std::shared_ptr<DAGNode> Parser::mkApplyFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params){
		std::shared_ptr<DAGNode> res = std::shared_ptr<DAGNode>(new DAGNode(fun->getSort(), NODE_KIND::NT_FUNC_APPLY, fun->getName()));
		res->updateApplyFunc(fun->getSort(), fun, params);
		static_functions.emplace_back(res);
		return res;
	}

	// QUANTIFIERS
	// (quantifier ((<identifier> <sort>)+） <expr>)
	std::shared_ptr<DAGNode> Parser::mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort){
		if(quant_var_map.find(name) != quant_var_map.end()){
			return quant_var_map[name];
		}
		else{
			std::shared_ptr<DAGNode> var = std::make_shared<DAGNode>(sort, NODE_KIND::NT_QUANT_VAR, name);
			quant_var_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, var));
			return var;
		}
	}
	void Parser::parseQuant(const std::string& type){
		// (quantifier ((<identifier> <sort>)+） <expr>)
		//             ^
		parseLpar();
		std::vector<std::shared_ptr<DAGNode>> params;
		while (*bufptr != ')') {
			// (quantifier ((<identifier> <sort>)+） <expr>)
			//              ^
			parseLpar();
			std::string var_name = getSymbol();
			std::shared_ptr<Sort> var_sort = parseSort();
			std::shared_ptr<DAGNode> var = mkQuantVar(var_name, var_sort);
			params.emplace_back(var);
			parseRpar();
		}
		// (quantifier ((<identifier> <sort>)+） <expr>)
		//                                    ^
		parseRpar();
		std::shared_ptr<DAGNode> body = parseExpr();
		params.insert(params.begin(), body);
		if (type == "forall") {
			mkForall(params);
		}
		else if (type == "exists") {
			mkExists(params);
		}
		else{
			cassert(false, "Invalid quantifier");
		}
	}

	std::shared_ptr<DAGNode> Parser::mkForall(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(BOOL_SORT, NODE_KIND::NT_FORALL, params);
	}
	std::shared_ptr<DAGNode> Parser::mkExists(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(BOOL_SORT, NODE_KIND::NT_EXISTS, params);
	}

	
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params){
		boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
		return substitute(expr, params, visited);
	}
	// visited is used to avoid infinite loop
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, boost::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, boost::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited){
		if( visited.find(expr) != visited.end()){
			return visited[expr];
		}
		if(expr->isVar()){
			if(params.find(expr->getName()) != params.end()){
				return params[expr->getName()];
			}
			else{
				return expr;
			}
		}
		else if(expr->isConst() || 
				expr->isFuncParam()){
			return expr;
		}
		else{
			std::vector<std::shared_ptr<DAGNode>> record;
			for(size_t i=0;i<expr->getChildrenSize();i++){
				record.emplace_back(substitute(expr->getChild(i), params, visited));
			}
			std::shared_ptr<DAGNode> res = mkOper(expr->getSort(), expr->getKind(), record);
			visited[expr] = res;
			return res;
		}
	}

	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr){
		bool is_changed = false;
		return arithNormalize(expr, is_changed);
	}


	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr, bool& is_changed){
		if(expr->isErr()){
			return expr;
		}
		// expand let
		if(expr->isLet()){
			expr = expandLet(expr);
		}
		
		if(expr->isArithTerm()){
			return expr;
		}
		if(expr->isConst()){
			return expr;
		}
		else if(expr->isVar()){
			return expr;
		}
		else if(expr->isArithComp()){
			cassert(expr->getChildrenSize() == 2, "ArithComp should have two children");
			std::shared_ptr<DAGNode> left_side = expr->getChild(0);
			std::shared_ptr<DAGNode> right_side = expr->getChild(1);
			cassert(left_side->isArithTerm() && right_side->isArithTerm(), "ArithComp should have two arith terms");
			if(right_side->isConst()){
				// no need to change
				is_changed = false;
				return expr;
			}
			else{
				// need to change
				is_changed = true;
				std::shared_ptr<DAGNode> left = mkOper(left_side->getSort(), NODE_KIND::NT_SUB, {left_side, right_side});
				return mkOper(BOOL_SORT, expr->getKind(), {left, getZero(left_side->getSort())});
			}
		}
		else{
			bool cur_is_changed = false;
			std::vector<std::shared_ptr<DAGNode>> record;
			for(size_t i=0;i<expr->getChildrenSize();i++){
				bool child_changed = false;
				record.emplace_back(arithNormalize(expr->getChild(i), child_changed));
				cur_is_changed = cur_is_changed || child_changed;
			}
			if(cur_is_changed){
				std::shared_ptr<DAGNode> res = mkOper(expr->getSort(), expr->getKind(), record);
				is_changed = true;
				return res;
			}
			else{
				is_changed = false;
				return expr;
			}
		}
	}

	std::vector<std::shared_ptr<DAGNode>> Parser::arithNormalize(std::vector<std::shared_ptr<DAGNode>> exprs){
		std::vector<std::shared_ptr<DAGNode>> res;
		for(auto& expr : exprs){
			res.emplace_back(arithNormalize(expr));
		}
		return res;
	}


	// aux functions
	NODE_KIND Parser::getAddOp(std::shared_ptr<Sort> sort){
		if(sort == INT_SORT || sort == REAL_SORT){
			return NODE_KIND::NT_ADD;
		}
		else if(sort->isBv()){
			return NODE_KIND::NT_BV_ADD;
		}
		else if(sort->isFp()){
			return NODE_KIND::NT_FP_ADD;
		}
		else{
			return NODE_KIND::NT_ERROR;
		}
	}
	NODE_KIND Parser::getOppositeKind(NODE_KIND kind){
		return SMTParser::getOppositeKind(kind);
	}
	std::shared_ptr<DAGNode> Parser::getZero(std::shared_ptr<Sort> sort){
		if(sort->isInt() || sort->isIntOrReal()){
			return mkConstInt(0);
		}
		else if(sort->isReal()){
			return mkConstReal(0.0);
		}
		else if(sort->isBv()){
			return mkConstBv("0", sort->getBitWidth());
		}
		else if(sort->isFp()){
			return mkConstFp("0.0", sort->getExponentWidth(), sort->getSignificandWidth());
		}
		else if(sort->isStr()){
			return mkConstStr("");
		}
		else{
			return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
		}
	}
	// error operations
	std::shared_ptr<DAGNode> Parser::mkErr(const ERROR_TYPE t){
		return std::make_shared<DAGNode>(NULL_SORT, (NODE_KIND)t);
	}
	void Parser::err_all(const ERROR_TYPE e, const std::string s, const size_t ln) const {
		switch (e) {
		case ERROR_TYPE::ERR_UNEXP_EOF:
			err_unexp_eof();
			break;
		case ERROR_TYPE::ERR_SYM_MIS:
			err_sym_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_UNKWN_SYM:
			err_unkwn_sym(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_MIS:
			err_param_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NBOOL:
			err_param_nbool(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NNUM:
			err_param_nnum(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NSAME:
			err_param_nsame(s, ln);
			break;
		case ERROR_TYPE::ERR_LOGIC:
			err_logic(s, ln);
			break;
		case ERROR_TYPE::ERR_MUL_DECL:
			err_mul_decl(s, ln);
			break;
		case ERROR_TYPE::ERR_MUL_DEF:
			err_mul_def(s, ln);
			break;
		case ERROR_TYPE::ERR_ZERO_DIVISOR:
			err_zero_divisor(ln);
			break;
		case ERROR_TYPE::ERR_FUN_LOCAL_VAR:
			err_param_nsame(s, ln);
			break;
		case ERROR_TYPE::ERR_ARI_MIS:
			err_arity_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_TYPE_MIS:
			err_type_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_NEG_PARAM:
			err_neg_param(ln);
			break;
		}
	}

	void Parser::err_all(const std::shared_ptr<DAGNode> e, const std::string s, const size_t ln) const {
		err_all((ERROR_TYPE)e->getKind(), s, ln);
	}

	// unexpected end of file
	void Parser::err_unexp_eof() const {
		std::cout << "error: Unexpected end of file found." << std::endl;
		exit(0);
	}

	// symbol missing
	void Parser::err_sym_mis(const std::string mis, const size_t ln) const {
		std::cout << "error: \"" << mis << "\" missing in line " << ln << '.' << std::endl;
		exit(0);
	}

	void Parser::err_sym_mis(const std::string mis, const std::string nm, const size_t ln) const {
		std::cout << "error: \"" << mis << "\" missing before \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// unknown symbol
	void Parser::err_unkwn_sym(const std::string nm, const size_t ln) const {
		if (nm == "") err_unexp_eof();
		std::cout << "error: Unknown or unexptected symbol \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// wrong number of parameters
	void Parser::err_param_mis(const std::string nm, const size_t ln) const {
		std::cout << "error: Wrong number of parameters of \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// paramerter type error
	void Parser::err_param_nbool(const std::string nm, const size_t ln) const {
		std::cout << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerter is not a boolean." << std::endl;
		exit(0);
	}

	void Parser::err_param_nnum(const std::string nm, const size_t ln) const {
		std::cout << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerter is not an integer or a real." << std::endl;
		exit(0);
	}

	// paramerters are not in same type
	void Parser::err_param_nsame(const std::string nm, const size_t ln) const {
		std::cout << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerters are not in same type." << std::endl;
		exit(0);
	}

	// logic doesnt support
	void Parser::err_logic(const std::string nm, const size_t ln) const {
		std::cout << "error: Logic does not support \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// multiple declaration
	void Parser::err_mul_decl(const std::string nm, const size_t ln) const {
		std::cout << "error: Multiple declarations of \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// multiple definition
	void Parser::err_mul_def(const std::string nm, const size_t ln) const {
		std::cout << "error: Multiple definitions or keybindings of \""
			<< nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// divisor is zero
	void Parser::err_zero_divisor(const size_t ln) const {
		std::cout << "error: Divisor is zero in line " << ln << '.' << std::endl;
		exit(0);
	}

	// arity mismatch
	void Parser::err_arity_mis(const std::string nm, const size_t ln) const{
		std::cout << "error: Arity mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	// kind mismatch
	void Parser::err_type_mis(const std::string nm, const size_t ln) const{
		std::cout << "error: Kind mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}


	void Parser::err_neg_param(const size_t ln) const{
		std::cout << "error: Negative parameter in line " << ln << '.' << std::endl;
		exit(0);
	}

	// keyword error
	void Parser::err_keyword(const std::string nm, const size_t ln) const{
		std::cout << "error: keyword mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		exit(0);
	}

	/*
	global errors
	*/
	// cannot open file
	void Parser::err_open_file(const std::string filename) const {
		std::cout << "error: Cannot open file \"" << filename << "\"." << std::endl;
		exit(0);
	}

	std::shared_ptr<DAGNode> Parser::rename(std::shared_ptr<DAGNode> expr, const std::string& new_name){
		cassert(expr->isVar(), "Only variable can be renamed");
		std::string old_name = expr->getName();
		if(expr->isTempVar()){
			size_t old_index = temp_var_names[old_name];
			temp_var_names[new_name] = old_index;
		}
		else{
			size_t old_index = var_names[old_name];
			var_names[new_name] = old_index;
		}
		expr->rename(new_name);

		return expr;
	}	

	std::string Parser::toString(std::shared_ptr<DAGNode> expr){
		return dumpSMTLIB2(expr);
	}

	std::string Parser::toString(std::shared_ptr<Sort> sort){
		return sort->toString();
	}

	std::string Parser::toString(const NODE_KIND& kind){
		return kindToString(kind);
	}

	std::string Parser::dumpSMT2(){
		std::stringstream ss;
		ss << "(set-logic " << options->getLogic() << ")" << std::endl;
		// variables
		std::vector<std::shared_ptr<DAGNode>> vars = getVariables();
		for(auto& var : vars){
			ss << "(declare-fun " << var->getName() << " () " << var->getSort()->toString() << ")" << std::endl;
		}
		std::vector<std::shared_ptr<DAGNode>> functions = getFunctions();
		for(auto& func : functions){
			ss << dumpFuncDef(func);
		}
		// constraints
		for(auto& constraint : assertions){
			ss << "(assert " << dumpSMTLIB2(constraint) << ")" << std::endl;
		}
		ss << "(check-sat)" << std::endl;
		ss << "(exit)" << std::endl;
		return ss.str();
	}

	std::string Parser::dumpSMT2(const std::string& filename){
		std::ofstream file(filename);
		file << dumpSMT2();
		file.close();
		return filename;
	}

	/*
	warnings
	*/
	// command not support
	void Parser::warn_cmd_nsup(const std::string nm, const size_t ln) const {
		std::cout << "warning: \"" << nm << "\" command is safely ignored in line " << ln << "." << std::endl;
	}

	ParserPtr newParser(){
		return std::make_shared<Parser>();
	}

	ParserPtr newParser(const std::string& filename){
		return std::make_shared<Parser>(filename);
	}
}
