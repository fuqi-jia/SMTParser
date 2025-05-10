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

#include "../include/parser.h"
#include <queue>
#include <stack>

namespace SMTLIBParser{

	Parser::Parser(){
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;

		err_node = std::make_shared<DAGNode>(UNKNOWN_SORT, NODE_KIND::NT_ERROR, "error");
		constants.insert(std::pair<std::string, size_t>("error", node_list.size()));
		node_list.emplace_back(err_node);
		false_node = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_FALSE, "false");
		constants.insert(std::pair<std::string, size_t>("false", node_list.size()));
		node_list.emplace_back(false_node);
		true_node = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_TRUE, "true");
		constants.insert(std::pair<std::string, size_t>("true", node_list.size()));
		node_list.emplace_back(true_node);
		
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

		err_node = std::make_shared<DAGNode>(UNKNOWN_SORT, NODE_KIND::NT_ERROR, "error");
		constants.insert(std::pair<std::string, size_t>("error", node_list.size()));
		node_list.emplace_back(err_node);
		false_node = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_FALSE, "false");
		constants.insert(std::pair<std::string, size_t>("false", node_list.size()));
		node_list.emplace_back(false_node);
		true_node = std::make_shared<DAGNode>(BOOL_SORT, NODE_KIND::NT_CONST_TRUE, "true");
		constants.insert(std::pair<std::string, size_t>("true", node_list.size()));
		node_list.emplace_back(true_node);
		
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
		return vars;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getFunctions() const{
		std::vector<std::shared_ptr<DAGNode>> funs;
		for(auto fun : function_names){
			funs.emplace_back(fun_key_map.at(fun));
		}
		return funs;
	}
	// parse smt-lib2 file
	std::string Parser::getSymbol() {

		char *beg = bufptr;

		// first char was already scanned
		bufptr++;

		// while not eof	
		while (*bufptr != 0) {

			switch (scan_mode) {
			case SCAN_MODE::SM_SYMBOL:
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

					// out of symbol mode by ';', '|', '(', and ')'
					std::string tmp_s(beg, bufptr - beg);
					return tmp_s;

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
				assert(false);
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

		// parse finished
		// let_key_map.clear();
		// fun_key_map.clear();
		// sort_key_map.clear();
		// var_names.clear();
		// constants.clear();
		bufptr = nullptr;
		delete[] buffer;
		return true;
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

			std::shared_ptr<DAGNode> expr = nullptr;
			if(s == "pi"){
				expr = mkPi();
			}
			else if(s == "e"){
				expr = mkE();
			}
			else if(s == "inf"){
				expr = mkInfinity();
			}
			else if(s == "epsion"){
				expr = mkEpsilon();
			}
			else if(s == "NaN"){
				expr = mkNan();
			}
			// support -3 (before only - 3)
			else if(isIntUtil(s)){
				// additional process -> constant can be real or integer
				// 0 -> Int or Real?
				expr = mkConstInt(s);
			}
			else if(isRealUtil(s)){
				expr = mkConstReal(s);
			}
			else if(isBVUtil(s)){
				expr = mkConstBv(s, s.size() - 2);
			}
			// else if(isFPUtil(s)){
			// 	expr = mkConstFP(s);
			// }
			else if(isStrUtil(s)){
				expr = mkConstStr(s);
			}
			else if (s == "true") {
				expr = mkTrue();
			}
			else if (s == "false") {
				expr = mkFalse();
			}
			else {
				if(let_key_map.find(s) != let_key_map.end()){
					expr = let_key_map[s];
				}
				else if(fun_key_map.find(s) != fun_key_map.end()){
					// function name
					expr = fun_key_map[s];
				}
				else if(fun_var_map.find(s) != fun_var_map.end()){
					// function variable name
					expr = fun_var_map[s];
				}
				else if(var_names.find(s) != var_names.end()){
					// variable name
					expr = node_list[var_names[s]];
				}
				// following Common Lisp's conventions, enclosing
				// a simple symbol in vertical bars does not produce a new symbol.
				else if(s.size() > 1 && 
						s[0] == '|'  && 
						s[s.size() - 1] == '|' &&
						var_names.find(s.substr(1, s.size() - 2)) != var_names.end()){
					// string
					expr = node_list[var_names[s.substr(1, s.size() - 2)]];
				}
				else err_unkwn_sym(s, expr_ln);
			}
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
				if (f == "extract") {
					assert(args.size() == 2);
					assert(params.size() == 1);
					expr = mkBvExtract(params[0], args[0], args[1]);
				}
				else if (f == "repeat") {
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkBvRepeat(params[0], args[0]);
				}
				else if (f == "zero_extend") {
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkBvZeroExt(params[0], args[0]);
				}
				else if (f == "sign_extend") {
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkBvSignExt(params[0], args[0]);
				}
				else if(f == "int_to_bv") {
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkIntToBv(params[0], args[0]);
				}
				else if(f == "rotate_left") {
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkBvRotateLeft(params[0], args[0]);
				}
				else if(f == "rotate_right"){
					assert(args.size() == 1);
					assert(params.size() == 1);
					expr = mkBvRotateRight(params[0], args[0]);
				}
				else err_unkwn_sym(s, expr_ln);
			}
			else err_unkwn_sym(s, expr_ln);
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
				if (s == "and") {
					expr = mkAnd(params);
				}
				else if (s == "or") {
					expr = mkOr(params);
				}
				else if (s == "not") {
					assert(params.size() == 1);
					expr = mkNot(params[0]);
				}
				else if (s == "=>") {
					expr = mkImplies(params);
				}
				else if (s == "xor") {
					expr = mkXor(params);
				}
				else if (s == "=") {
					expr = mkEq(params);
				}
				else if (s == "distinct") {
					expr = mkDistinct(params);
				}
				else if (s == "ite") {
					expr = mkIte(params);
				}
				else if (s == "+") {
					expr = mkAdd(params);
				}
				else if (s == "-") {
					expr = mkSub(params);
				}
				else if (s == "*") {
					expr = mkMul(params);
				}
				else if (s == "iand") {
					expr = mkIand(params);
				}
				else if (s == "pow2") {
					assert(params.size() == 1);
					expr = mkPow2(params[0]);
				}
				else if (s == "pow") {
					assert(params.size() == 2);
					expr = mkPow(params[0], params[1]);
				}
				else if (s == "div") {
					assert(params.size() == 2);
					expr = mkDivInt(params[0], params[1]);
				}
				else if (s == "/") {
					assert(params.size() == 2);
					expr = mkDivReal(params[0], params[1]);
				}
				else if (s == "mod") {
					assert(params.size() == 2);
					expr = mkMod(params[0], params[1]);
				}
				else if (s == "abs") {
					assert(params.size() == 1);
					expr = mkAbs(params[0]);
				}
				else if (s == "sqrt") {
					assert(params.size() == 1);
					expr = mkSqrt(params[0]);
				}
				else if (s == "ceil") {
					assert(params.size() == 1);
					expr = mkCeil(params[0]);
				}
				else if (s == "floor") {
					assert(params.size() == 1);
					expr = mkFloor(params[0]);
				}
				else if (s == "round") {
					assert(params.size() == 1);
					expr = mkRound(params[0]);
				}
				else if (s == "exp") {
					assert(params.size() == 1);
					expr = mkExp(params[0]);
				}
				else if (s == "ln") {
					assert(params.size() == 1);
					expr = mkLn(params[0]);
				}
				else if (s == "lg") {
					assert(params.size() == 1);
					expr = mkLg(params[0]);
				}
				else if (s == "log") {
					assert(params.size() == 2);
					expr = mkLog(params[0], params[1]);
				}
				else if (s == "sin") {
					assert(params.size() == 1);
					expr = mkSin(params[0]);
				}
				else if (s == "cos") {
					assert(params.size() == 1);
					expr = mkCos(params[0]);
				}
				else if (s == "tan") {
					assert(params.size() == 1);
					expr = mkTan(params[0]);
				}
				else if (s == "asin" || s == "arcsin") {
					assert(params.size() == 1);
					expr = mkAsin(params[0]);
				}
				else if (s == "acos" || s == "arccos") {
					assert(params.size() == 1);
					expr = mkAcos(params[0]);
				}
				else if (s == "atan" || s == "arctan") {
					assert(params.size() == 1);
					expr = mkAtan(params[0]);
				}
				else if (s == "atan2" || s == "arctan2") {
					assert(params.size() == 2);
					expr = mkAtan2(params[0], params[1]);
				}
				else if (s == "sinh") {
					assert(params.size() == 1);
					expr = mkSinh(params[0]);
				}
				else if (s == "cosh") {
					assert(params.size() == 1);
					expr = mkCosh(params[0]);
				}
				else if (s == "tanh") {
					assert(params.size() == 1);
					expr = mkTanh(params[0]);
				}
				else if (s == "asinh") {
					assert(params.size() == 1);
					expr = mkAsinh(params[0]);
				}
				else if (s == "acosh") {
					assert(params.size() == 1);
					expr = mkAcosh(params[0]);
				}
				else if (s == "atanh") {
					assert(params.size() == 1);
					expr = mkAtanh(params[0]);
				}
				else if (s == "asech") {
					assert(params.size() == 1);
					expr = mkAsech(params[0]);
				}
				else if (s == "acsch") {
					assert(params.size() == 1);
					expr = mkAcsch(params[0]);
				}
				else if (s == "acoth") {
					assert(params.size() == 1);
					expr = mkAcoth(params[0]);
				}
				else if (s == "<=") {
					assert(params.size() == 2);
					expr = mkLe(params[0], params[1]);
				}
				else if (s == "<") {
					assert(params.size() == 2);
					expr = mkLt(params[0], params[1]);
				}
				else if (s == ">=") {
					assert(params.size() == 2);
					expr = mkGe(params[0], params[1]);
				}
				else if (s == ">") {
					assert(params.size() == 2);
					expr = mkGt(params[0], params[1]);
				}
				else if (s == "to_real") {
					assert(params.size() == 1);
					expr = mkToReal(params[0]);
				}
				else if (s == "to_int") {
					assert(params.size() == 1);
					expr = mkToInt(params[0]);
				}
				else if (s == "is_int") {
					assert(params.size() == 1);
					expr = mkIsInt(params[0]);
				}
				else if (s == "is_divisible") {
					assert(params.size() == 2);
					expr = mkIsDivisible(params[0], params[1]);
				}
				else if (s == "is_prime") {
					assert(params.size() == 1);
					expr = mkIsPrime(params[0]);
				}
				else if (s == "is_even") {
					assert(params.size() == 1);
					expr = mkIsEven(params[0]);
				}
				else if (s == "is_odd") {
					assert(params.size() == 1);
					expr = mkIsOdd(params[0]);
				}
				else if (s == "gcd") {
					assert(params.size() == 2);
					expr = mkGcd(params[0], params[1]);
				}
				else if (s == "lcm") {
					assert(params.size() == 2);
					expr = mkLcm(params[0], params[1]);
				}
				else if (s == "factorial") {
					assert(params.size() == 1);
					expr = mkFact(params[0]);
				}
				else if (s == "bvnot") {
					assert(params.size() == 1);
					expr = mkBvNot(params[0]);
				}
				else if (s == "bvneg") {
					assert(params.size() == 1);
					expr = mkBvNeg(params[0]);
				}
				else if (s == "bvand") {
					expr = mkBvAnd(params);
				}
				else if (s == "bvor") {
					expr = mkBvOr(params);
				}
				else if (s == "bvxor") {
					expr = mkBvXor(params);
				}
				else if (s == "bvnand") {
					expr = mkBvNand(params);
				}
				else if (s == "bvnor") {
					expr = mkBvNor(params);
				}
				else if (s == "bvxnor") {
					expr = mkBvXnor(params);
				}
				else if (s == "bvcomp") {
					assert(params.size() == 2);
					expr = mkBvComp(params[0], params[1]);
				}
				else if (s == "bvadd") {
					expr = mkBvAdd(params);
				}
				else if (s == "bvsub") {
					expr = mkBvSub(params);
				}
				else if (s == "bvmul") {
					expr = mkBvMul(params);
				}
				else if (s == "bvudiv") {
					assert(params.size() == 2);
					expr = mkBvUdiv(params[0], params[1]);
				}
				else if (s == "bvurem") {
					assert(params.size() == 2);
					expr = mkBvUrem(params[0], params[1]);
				}
				else if (s == "bvsdiv") {
					assert(params.size() == 2);
					expr = mkBvSdiv(params[0], params[1]);
				}
				else if (s == "bvsrem") {
					assert(params.size() == 2);
					expr = mkBvSrem(params[0], params[1]);
				}
				else if (s == "bvsmod") {
					assert(params.size() == 2);
					expr = mkBvSmod(params[0], params[1]);
				}
				else if (s == "bvshl") {
					assert(params.size() == 2);
					expr = mkBvShl(params[0], params[1]);
				}
				else if (s == "bvlshr") {
					assert(params.size() == 2);
					expr = mkBvLshr(params[0], params[1]);
				}
				else if (s == "bvashr") {
					assert(params.size() == 2);
					expr = mkBvAshr(params[0], params[1]);
				}
				else if (s == "bvult") {
					assert(params.size() == 2);
					expr = mkBvUlt(params[0], params[1]);
				}
				else if (s == "bvule") {
					assert(params.size() == 2);
					expr = mkBvUle(params[0], params[1]);
				}
				else if (s == "bvugt") {
					assert(params.size() == 2);
					expr = mkBvUgt(params[0], params[1]);
				}
				else if (s == "bvuge") {
					assert(params.size() == 2);
					expr = mkBvUge(params[0], params[1]);
				}
				else if (s == "bvslt") {
					assert(params.size() == 2);
					expr = mkBvSlt(params[0], params[1]);
				}
				else if (s == "bvsle") {
					assert(params.size() == 2);
					expr = mkBvSle(params[0], params[1]);
				}
				else if (s == "bvsgt") {
					assert(params.size() == 2);
					expr = mkBvSgt(params[0], params[1]);
				}
				else if (s == "bvsge") {
					assert(params.size() == 2);
					expr = mkBvSge(params[0], params[1]);
				}
				else if (s == "concat") {
					expr = mkBvConcat(params);
				}
				else if (s == "bv2nat") {
					assert(params.size() == 1);
					expr = mkBvToNat(params[0]);
				}
				else if (s == "nat2bv") {
					assert(params.size() == 2);
					expr = mkNatToBv(params[0], params[1]);
				}
				else if (s == "int2bv") {
					assert(params.size() == 2);
					expr = mkIntToBv(params[0], params[1]);
				}
				else if (s == "bv2int") {
					assert(params.size() == 1);
					expr = mkBvToInt(params[0]);
				}
				else if (s == "fp.abs") {
					assert(params.size() == 1);
					expr = mkFpAbs(params[0]);
				}
				else if (s == "fp.neg") {
					assert(params.size() == 1);
					expr = mkFpNeg(params[0]);
				}
				else if (s == "fp.add") {
					expr = mkFpAdd(params);
				}
				else if (s == "fp.sub") {
					expr = mkFpSub(params);
				}
				else if (s == "fp.mul") {
					expr = mkFpMul(params);
				}
				else if (s == "fp.div") {
					expr = mkFpDiv(params);
				}
				else if (s == "fp.fma") {
					assert(params.size() == 3);
					expr = mkFpFma(params);
				}
				else if (s == "fp.sqrt") {
					assert(params.size() == 1);
					expr = mkFpSqrt(params[0]);
				}
				else if (s == "fp.rem") {
					assert(params.size() == 2);
					expr = mkFpRem(params[0], params[1]);
				}
				else if (s == "fp.roundToIntegral") {
					assert(params.size() == 1);
					expr = mkFpRoundToIntegral(params[0]);
				}
				else if (s == "fp.min") {
					assert(params.size() == 2);
					expr = mkFpMin(params);
				}
				else if (s == "fp.max") {
					assert(params.size() == 2);
					expr = mkFpMax(params);
				}
				else if (s == "fp.leq") {
					assert(params.size() == 2);
					expr = mkFpLe(params[0], params[1]);
				}
				else if (s == "fp.lt") {
					assert(params.size() == 2);
					expr = mkFpLt(params[0], params[1]);
				}
				else if (s == "fp.geq") {
					assert(params.size() == 2);
					expr = mkFpGe(params[0], params[1]);
				}
				else if (s == "fp.gt") {
					assert(params.size() == 2);
					expr = mkFpGt(params[0], params[1]);
				}
				else if (s == "fp.eq") {
					assert(params.size() == 2);
					expr = mkFpEq(params[0], params[1]);
				}
				else if (s == "fp.to_ubv") {
					assert(params.size() == 2);
					expr = mkFpToUbv(params[0], params[1]);
				}
				else if (s == "fp.to_sbv") {
					assert(params.size() == 2);
					expr = mkFpToSbv(params[0], params[1]);
				}
				else if (s == "fp.to_real") {
					assert(params.size() == 1);
					expr = mkFpToReal(params[0]);
				}
				else if (s == "to_fp") {
					assert(params.size() == 3);
					expr = mkToFp(params[0], params[1], params[2]);
				}
				else if (s == "fp.isNormal"){
					assert(params.size() == 1);
					expr = mkFpIsNormal(params[0]);
				}
				else if (s == "fp.isSubnormal"){
					assert(params.size() == 1);
					expr = mkFpIsSubnormal(params[0]);
				}
				else if (s == "fp.isZero"){
					assert(params.size() == 1);
					expr = mkFpIsZero(params[0]);
				}
				else if (s == "fp.isInfinite"){
					assert(params.size() == 1);
					expr = mkFpIsInf(params[0]);
				}
				else if (s == "fp.isNaN"){
					assert(params.size() == 1);
					expr = mkFpIsNan(params[0]);
				}
				else if (s == "fp.isNegative"){
					assert(params.size() == 1);
					expr = mkFpIsNeg(params[0]);
				}
				else if (s == "fp.isPositive"){
					assert(params.size() == 1);
					expr = mkFpIsPos(params[0]);
				}
				else if (s == "select") {
					assert(params.size() == 2);
					expr = mkSelect(params[0], params[1]);
				}
				else if (s == "store") {
					assert(params.size() == 3);
					expr = mkStore(params[0], params[1], params[2]);
				}
				else if (s == "str.len") {
					assert(params.size() == 1);
					expr = mkStrLen(params[0]);
				}
				else if (s == "str.++") {
					expr = mkStrConcat(params);
				}
				else if (s == "str.substr") {
					assert(params.size() == 3);
					expr = mkStrSubstr(params[0], params[1], params[2]);
				}
				else if (s == "str.prefixof") {
					assert(params.size() == 2);
					expr = mkStrPrefixof(params[0], params[1]);
				}
				else if (s == "str.suffixof") {
					assert(params.size() == 2);
					expr = mkStrSuffixof(params[0], params[1]);
				}
				else if (s == "str.indexof") {
					assert(params.size() == 3);
					expr = mkStrIndexof(params[0], params[1], params[2]);
				}
				else if (s == "str.at") {
					assert(params.size() == 2);
					expr = mkStrCharat(params[0], params[1]);
				}
				else if (s == "str.update") {
					assert(params.size() == 3);
					expr = mkStrUpdate(params[0], params[1], params[2]);
				}
				else if (s == "str.replace") {
					assert(params.size() == 3);
					expr = mkStrReplace(params[0], params[1], params[2]);
				}
				else if (s == "str.replace_all") {
					assert(params.size() == 3);
					expr = mkStrReplaceAll(params[0], params[1], params[2]);
				}
				else if (s == "str.to_lower") {
					assert(params.size() == 1);
					expr = mkStrToLower(params[0]);
				}
				else if (s == "str.to_upper") {
					assert(params.size() == 1);
					expr = mkStrToUpper(params[0]);
				}
				else if (s == "str.rev") {
					assert(params.size() == 1);
					expr = mkStrRev(params[0]);
				}
				else if (s == "str.split") {
					assert(params.size() == 2);
					expr = mkStrSplit(params[0], params[1]);
				}
				else if (s == "str.<"){
					assert(params.size() == 2);
					expr = mkStrLt(params[0], params[1]);
				}
				else if (s == "str.<="){
					assert(params.size() == 2);
					expr = mkStrLe(params[0], params[1]);
				}
				else if (s == "str.>"){
					assert(params.size() == 2);
					expr = mkStrGt(params[0], params[1]);
				}
				else if (s == "str.>="){
					assert(params.size() == 2);
					expr = mkStrGe(params[0], params[1]);
				}
				else if (s == "str.in_re"){
					assert(params.size() == 2);
					expr = mkStrInReg(params[0], params[1]);
				}
				else if (s == "str.contains"){
					assert(params.size() == 2);
					expr = mkStrContains(params[0], params[1]);
				}
				else if (s == "str.is_digit"){
					assert(params.size() == 1);
					expr = mkStrIsDigit(params[0]);
				}
				else if (s == "str.from_int"){
					assert(params.size() == 1);
					expr = mkStrFromInt(params[0]);
				}
				else if (s == "str.to_int"){
					assert(params.size() == 1);
					expr = mkStrToInt(params[0]);
				}
				else if (s == "str.to_re"){
					assert(params.size() == 1);
					expr = mkStrToReg(params[0]);
				}
				else if (s == "str.to_code"){
					assert(params.size() == 1);
					expr = mkStrToCode(params[0]);
				}
				else if (s == "str.from_code"){
					assert(params.size() == 1);
					expr = mkStrFromCode(params[0]);
				}
				else if (s == "re.none"){
					expr = mkRegNone();
				}
				else if (s == "re.all"){
					expr = mkRegAll();
				}
				else if (s == "re.allchar"){
					expr = mkRegAllChar();
				}
				else if (s == "re.++") {
					expr = mkRegConcat(params);
				}
				else if (s == "re.union") {
					expr = mkRegUnion(params);
				}
				else if (s == "re.inter") {
					expr = mkRegInter(params);
				}
				else if (s == "re.diff") {
					expr = mkRegDiff(params);
				}
				else if (s == "re.*") {
					assert(params.size() == 1);
					expr = mkRegStar(params[0]);
				}
				else if (s == "re.+") {
					assert(params.size() == 1);
					expr = mkRegPlus(params[0]);
				}
				else if (s == "re.?") {
					assert(params.size() == 1);
					expr = mkRegOpt(params[0]);
				}
				else if (s == "re.range") {
					assert(params.size() == 2);
					expr = mkRegRange(params[0], params[1]);
				}
				else if (s == "re.repeat") {
					assert(params.size() == 2);
					expr = mkRegRepeat(params[0], params[1]);
				}
				else if (s == "re.loop") {
					assert(params.size() == 3);
					expr = mkRegLoop(params[0], params[1], params[2]);
				}
				else if (s == "re.complement") {
					assert(params.size() == 1);
					expr = mkRegComplement(params[0]);
				}
				else if (fun_key_map.find(s) != fun_key_map.end()) {
					// function
					expr = applyFun(fun_key_map[s], params);
				}
				else err_unkwn_sym(s, expr_ln);

				// check error
				if (expr->isErr()) err_all(expr, s, expr_ln);
			}
		}
		parseRpar();

		return expr;

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
		stateStack.push_back(LetContext(0));
		
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
				assert(let_key == "let");
				parseLpar();  // Consume the second let expression's starting '('
				
				stateStack.push_back(LetContext(currentState.nesting_level + 1));
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
		if (fun->getChildrenSize() != params.size()){
			return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
		}

		if(fun->getFuncBody()->isErr()){
			return fun->getFuncBody();
		}
		
		// variable map for local variables
		boost::unordered_map<std::string, std::shared_ptr<DAGNode>> new_params_map;
		for (size_t i = 1; i < fun->getChildrenSize(); i++) {
			if(params[i]->isErr()){
				return params[i];
			}
			new_params_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(fun->getChild(i)->getName(), params[i - 1]));
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
					childResults.push_back(results[current->getChild(i)]);
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
						funcParams.push_back(current->getChild(i));
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
			assert(false);
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
		if(expr->isVar() && params.find(expr->getName()) != params.end()){
			return params[expr->getName()];
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
	std::shared_ptr<DAGNode> Parser::getZero(std::shared_ptr<Sort> sort){
		if(sort == INT_SORT){
			return mkConstInt("0");
		}
		else if(sort == REAL_SORT){
			return mkConstReal("0.0");
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


	/*
	warnings
	*/
	// command not support
	void Parser::warn_cmd_nsup(const std::string nm, const size_t ln) const {
		std::cout << "warning: \"" << nm << "\" command is safely ignored in line " << ln << "." << std::endl;
	}
}
