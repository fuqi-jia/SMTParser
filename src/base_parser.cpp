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
#include "timing.h"
#include <queue>
#include <stack>
#include <algorithm>

namespace SMTParser{

	Parser::Parser(){
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;
		preserving_let_counter = 0;
		let_nesting_depth = 0;
		temp_var_counter = 0;
		parsing_file = false;
		in_quantifier_scope = false;
		allow_placeholder_vars = false;
		placeholder_var_sort = nullptr;
		quant_nesting_depth = 0;
		node_manager = std::make_shared<NodeManager>();
		sort_manager = std::make_shared<SortManager>();
		options = std::make_shared<GlobalOptions>();

		// reverse
		let_key_map.reserve(1024);
		preserving_let_key_map.reserve(1024);
		fun_key_map.reserve(1024);
		fun_var_map.reserve(1024);
		sort_key_map.reserve(1024);
		quant_var_map.reserve(1024);
		static_functions.reserve(1024);
		var_names.reserve(1024);
		temp_var_names.reserve(1024);
		function_names.reserve(1024);
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
		preserving_let_counter = 0;
		let_nesting_depth = 0;
		temp_var_counter = 0;
		parsing_file = true;
		in_quantifier_scope = false;
		allow_placeholder_vars = false;
		placeholder_var_sort = nullptr;
		quant_nesting_depth = 0;
		node_manager = std::make_shared<NodeManager>();
		sort_manager = std::make_shared<SortManager>();
		options = std::make_shared<GlobalOptions>();

		// reverse
		let_key_map.reserve(1024);
		preserving_let_key_map.reserve(1024);
		fun_key_map.reserve(1024);
		fun_var_map.reserve(1024);
		sort_key_map.reserve(1024);
		quant_var_map.reserve(1024);
		static_functions.reserve(1024);
		var_names.reserve(1024);
		temp_var_names.reserve(1024);
		function_names.reserve(1024);

		parseSmtlib2File(filename);
	}

	Parser::~Parser() {	}

	RESULT_TYPE Parser::getResultType(){
		return result_type;
	}

	std::shared_ptr<DAGNode> Parser::getResult(){
		return result_node;
	}
	
	RESULT_TYPE Parser::checkSat(){
		if(result_type != RESULT_TYPE::RT_UNKNOWN){
			return result_type;
		}

		// simple check
		bool all_true = true;
		for(auto& assertion : assertions){
			if(assertion->isErr()){
				result_type = RESULT_TYPE::RT_ERROR;
				return result_type;
			}
			else if(assertion->isFalse()){
				all_true = false;
				return RESULT_TYPE::RT_UNSAT;
			}
			else if(assertion->isTrue()){
				continue;
			}
			else{
				// unknown assertion
				result_type = RESULT_TYPE::RT_UNKNOWN;
				return result_type;
			}
		}
		if(all_true){
			result_type = RESULT_TYPE::RT_SAT;
		}
		return result_type;
	}
	
	std::shared_ptr<Model> Parser::getModel(){
		return result_model;
	}

	size_t Parser::getNodeCount(){
		// return node_manager->size();
		// BFS to count the number of nodes
		// only count the nodes in assertions, assumptions, soft_assertions, soft_weights, objectives
		std::unordered_set<std::shared_ptr<DAGNode>> visited;
		std::queue<std::shared_ptr<DAGNode>> q;
		for(size_t i=0;i<assertions.size();i++){
			auto node = assertions[i];
			q.push(node);
			visited.insert(node);
		}
		for(size_t i=0;i<assumptions.size();i++){
			for(size_t j=0;j<assumptions[i].size();j++){
				auto node = assumptions[i][j];
				q.push(node);
				visited.insert(node);
			}
		}
		for(size_t i=0;i<soft_assertions.size();i++){
			auto node = soft_assertions[i];
			q.push(node);
			visited.insert(node);
		}
		for(size_t i=0;i<soft_weights.size();i++){
			auto node = soft_weights[i];
			q.push(node);
			visited.insert(node);
		}
		for(size_t i=0;i<objectives.size();i++){
			auto node = objectives[i]->getObjectiveTerm();
			q.push(node);
			visited.insert(node);
		}
		while(!q.empty()){
			auto node = q.front();
			q.pop();
			for(size_t i=0;i<node->getChildrenSize();i++){
				auto child = node->getChild(i);
				if(visited.find(child) == visited.end()){
					visited.insert(child);
					q.push(child);
				}
			}
		}
		return visited.size();
	}
	
	// to solver
	std::vector<std::shared_ptr<DAGNode>> Parser::getAssertions() const{
		return assertions;
	}
	std::unordered_map<std::string, std::unordered_set<size_t>> Parser::getGroupedAssertions() const{
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
	std::unordered_map<std::string, std::unordered_set<size_t>> Parser::getGroupedSoftAssertions() const{
		return soft_assertion_groups;
	}
	std::vector<std::shared_ptr<Objective>> Parser::getObjectives() const{
		return objectives;
	}
	
	void Parser::setOption(const std::string& key, const std::string& value){
		options->setOption(key, value);
	}
	void Parser::setOption(const std::string& key, const int& value){
		options->setOption(key, std::to_string(value));
	}
	void  Parser::setOption(const std::string& key, const double& value){
		options->setOption(key, std::to_string(value));
	}
	void Parser::setOption(const std::string& key, const bool& value){
		options->setOption(key, value?"true":"false");
	}
	std::shared_ptr<GlobalOptions> Parser::getOptions() const{
		return options;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		for(auto& var : var_names){
			vars.emplace_back(node_manager->getNode(var.second));
		}
		for(auto& var : temp_var_names){
			vars.emplace_back(node_manager->getNode(var.second));
		}
		return vars;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getDeclaredVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		for(auto& var : var_names){
			vars.emplace_back(node_manager->getNode(var.second));
		}
		return vars;
	}
	std::shared_ptr<DAGNode> Parser::getVariable(const std::string& var_name){
		if(var_names.find(var_name) != var_names.end()){
			return node_manager->getNode(var_names.at(var_name));
		}
		else if(temp_var_names.find(var_name) != temp_var_names.end()){
			return node_manager->getNode(temp_var_names.at(var_name));
		}
		return NodeManager::NULL_NODE;
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
		ensureNumberValue(expr);
		condAssert(expr->isCReal() || expr->isCInt(), "Cannot convert non-constant expression to real");
		if(expr->isPi()) return Real::pi(getEvaluatePrecision());
		if(expr->isE()) return Real::e(getEvaluatePrecision());
		return expr->getValue()->getNumberValue().toReal(getEvaluatePrecision());
	}
	Integer Parser::toInt(std::shared_ptr<DAGNode> expr){
		ensureNumberValue(expr);
		condAssert(expr->isCInt(), "Cannot convert non-integer expression to integer");
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

	void Parser::ensureNumberValue(std::shared_ptr<DAGNode> expr){
		if(!expr || !expr->isConst()) return;
		if(expr->getValue()!=nullptr) return;

		std::string s = expr->toString();
		try{
			if(TypeChecker::isInt(s)){
				Integer i(s);
				expr->setValue(i);
			}
			else if(TypeChecker::isReal(s)){
				// dynamic precision
				size_t digits = 0;
				for(char c: s){ if(std::isdigit(c)) digits++; }
				mpfr_prec_t prec = digits*4 + 16;
				Real r(s, prec);
				expr->setValue(r);
			}
		}catch(...){
			// raise error
			err_all(expr, "Cannot convert non-number expression to number", line_number);
		}
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
						if (TypeChecker::isReal(mantissa)) {
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
					// process the nested quotes - check if it is an escape quote
					if (bufptr + 1 < buffer + buflen && *(bufptr + 1) == '"') {
						// two consecutive quotes are escape quotes, skip the second quote
						bufptr++;
					} else {
						// end of string
						bufptr++;
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						scanToNextSymbol();
						return tmp_s;
					}
				}
				break;

			default:
				condAssert(false, "Invalid scan mode");
			}

			// go next char
			bufptr++;
		}

		if(parsing_file){
			err_unexp_eof();
		}
		else{
			std::string tmp_s(beg, bufptr - beg);
			// skip space
			scanToNextSymbol();
			return tmp_s;
		}

		return "";
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
		parsing_file = true;
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
		buffer = nullptr;
		return true;
	}

	char* safe_strdup(const std::string& str) {
		if (str.empty()) return nullptr;
		
		char* new_str = new (std::nothrow) char[str.length() + 1];
		if (!new_str) return nullptr;
		
		std::memcpy(new_str, str.c_str(), str.length() + 1);
		return new_str;
	}

	bool Parser::parseStr(const std::string& constraint) {
		buffer = safe_strdup(constraint);
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
		delete[] buffer;
		buffer = nullptr;
		return true;
	}

	bool Parser::assert(const std::string& constraint) {
		parsing_file = false;
		std::shared_ptr<DAGNode> expr = mkExpr(constraint);
		assertions.emplace_back(expr);
		return true;
	}

	bool Parser::assert(std::shared_ptr<DAGNode> node) {
		assertions.emplace_back(node);
		return true;
	}

	std::shared_ptr<DAGNode> Parser::mkExpr(const std::string& expression) {
		parsing_file = false;
		if (expression.empty()) {
			return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
		}
		
		buffer = safe_strdup(expression);
		if (!buffer) {
			return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
		}
		
		buflen = expression.length();
		bufptr = buffer;
		if (buflen > 0) line_number = 1;
		scanToNextSymbol();
		std::shared_ptr<DAGNode> expr = parseExpr();
		
		bufptr = nullptr;
		delete[] buffer;
		buffer = nullptr;
		return expr;
	}
	

	KEYWORD Parser::parseKeyword(){
		
		size_t key_ln = line_number;
		//std::cout << "line_number = " << key_ln << std::endl;
		std::string key = getSymbol();
		//std::cout << "key = " << key << std::endl;
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
		}else if (key == ":named"){
			return KEYWORD::KW_NAMED;
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
			std::string named_name = "";

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
			if (named_name == ""){
				KEYWORD key_ = attemptParseKeywords();
				if(key_ == KEYWORD::KW_NAMED){
					// (assert <expr> (! expr :named <symbol>))
					named_name = getSymbol();
				}
			}
			// if grp_id is not empty, insert to assertion_groups
			if(grp_id != ""){
				if(assertion_groups.find(grp_id) == assertion_groups.end()){
					assertion_groups.insert(std::pair<std::string, std::unordered_set<size_t>>(grp_id, {index}));
				}
				else{
					assertion_groups[grp_id].insert(index);
				}
			}
			//if named_name is not empty, insert to named_assertions
			if (named_name != ""){
				named_assertions[named_name] = assert_expr;
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
				if(!res->isErr()){
					function_names.emplace_back(name);
				}
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

		// (define-const <symbol> <sort> <expr>)
		if (command == "define-const") {
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

			// get returned type and body
			std::shared_ptr<Sort> out_sort = parseSort();
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::vector<std::shared_ptr<DAGNode>> params; // empty params for constant
			std::shared_ptr<DAGNode> res = mkFuncDef(name, params, out_sort, func_body);
			skipToRpar();
			
			return CMD_TYPE::CT_DEFINE_FUN;
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
			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			if(fun_key_map.find(name) != fun_key_map.end()){
				std::shared_ptr<DAGNode> check_fun = fun_key_map[name];
				if(check_fun->getKind() == NODE_KIND::NT_FUNC_DEF){
					err_mul_def(name, name_ln);
				}
				return CMD_TYPE::CT_DEFINE_FUN_REC;
			}
			// keep the function name with the same order
			function_names.emplace_back(name);

			// parse ((x Int))
			//       ^
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> params;
			std::vector<std::string> key_list;
			std::vector<std::shared_ptr<Sort>> param_sorts;
			while(*bufptr!=')'){ // there are still (x Int) left.
				// (x Int)
				// ^
				parseLpar();
				std::string pname = getSymbol();
				std::shared_ptr<Sort> ptype = parseSort();
				key_list.emplace_back(pname);
				param_sorts.emplace_back(ptype);
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
			
			//(define-fun-rec <symbol> ((<symbol> <sort>)*) <sort> <expr>)
			//					                        ^
			parseRpar();

			//get returned type
			std::shared_ptr<Sort> out_sort = parseSort();
			
			// For recursive functions, we need to create a function declaration first
			// so it can be referenced in its own body
			std::shared_ptr<DAGNode> func_dec = mkFuncDec(name, param_sorts, out_sort);
			
			// Now parse the function body (which can reference the function itself)
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::shared_ptr<DAGNode> res = mkFuncRec(name, params, out_sort, func_body);
			skipToRpar();

			//remove key bindings: for let uses local variables. 
			while (key_list.size() > 0) {
				fun_var_map.erase(key_list.back());
				key_list.pop_back();
			}
			
			return CMD_TYPE::CT_DEFINE_FUN_REC;
		}

		if (command == "define-funs-rec") {
			// (define-funs-rec ((name1 ((param1 type1)...) ret_type1)...) (body1 body2...))
			
			// Parse function declarations first
			parseLpar(); // for function declarations list
			std::vector<std::string> func_names;
			std::vector<std::vector<std::shared_ptr<DAGNode>>> all_params;
			std::vector<std::vector<std::string>> all_key_lists;
			std::vector<std::vector<std::shared_ptr<Sort>>> all_param_sorts;
			std::vector<std::shared_ptr<Sort>> return_sorts;
			
			while(*bufptr != ')') {
				// Parse each function declaration: (name ((param1 type1)...) ret_type)
				parseLpar();
				std::string name = getSymbol();
				
				if(fun_key_map.find(name) != fun_key_map.end()){
					std::shared_ptr<DAGNode> check_fun = fun_key_map[name];
					if(check_fun->getKind() == NODE_KIND::NT_FUNC_DEF){
						err_mul_def(name, line_number);
					}
					skipToRpar();
					continue;
				}
				
				func_names.emplace_back(name);
				function_names.emplace_back(name);
				
				// Parse parameters: ((param1 type1)...)
				parseLpar();
				std::vector<std::shared_ptr<DAGNode>> params;
				std::vector<std::string> key_list;
				std::vector<std::shared_ptr<Sort>> param_sorts;
				
				while(*bufptr != ')') {
					parseLpar();
					std::string pname = getSymbol();
					std::shared_ptr<Sort> ptype = parseSort();
					key_list.emplace_back(pname);
					param_sorts.emplace_back(ptype);
					std::shared_ptr<DAGNode> expr = mkFunParamVar(ptype, pname);
					params.emplace_back(expr);
					parseRpar();
				}
				parseRpar(); // end of parameters
				
				// Parse return type
				std::shared_ptr<Sort> out_sort = parseSort();
				return_sorts.emplace_back(out_sort);
				
				all_params.emplace_back(params);
				all_key_lists.emplace_back(key_list);
				all_param_sorts.emplace_back(param_sorts);
				
				parseRpar(); // end of function declaration
			}
			parseRpar(); // end of function declarations list
			
			// Create function declarations for all functions first
			// so they can be referenced in each other's bodies
			for(size_t i = 0; i < func_names.size(); i++) {
				mkFuncDec(func_names[i], all_param_sorts[i], return_sorts[i]);
			}
			
			// Parse function bodies
			parseLpar(); // for function bodies list
			for(size_t i = 0; i < func_names.size(); i++) {
				// Add parameter bindings for this function
				for(size_t j = 0; j < all_key_lists[i].size(); j++) {
					fun_var_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(
						all_key_lists[i][j], all_params[i][j]));
				}
				
				// Parse function body
				std::shared_ptr<DAGNode> func_body = parseExpr();
				std::shared_ptr<DAGNode> res = mkFuncRec(func_names[i], all_params[i], return_sorts[i], func_body);
				
				// Remove parameter bindings for this function
				for(const auto& key : all_key_lists[i]) {
					fun_var_map.erase(key);
				}
			}
			parseRpar(); // end of function bodies list
			
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_FUNS_REC;
		}

		// (define-sort <symbol> (<symbol>*) <sort>)
		// <symbol>* is a list of symbols that represent template parameters.
		// for example, (define-sort List (T) (List T))
		// T is a template parameter.
		// then (define-sort IntList () (List Int)) is a valid command.
		if (command == "define-sort") {
			// get name
			std::string name = getSymbol();

			// get params (symbols)
			std::vector<std::string> param_names;
			parseLpar();
			while(*bufptr != ')'){
				param_names.push_back(getSymbol());
			}
			parseRpar();
			
			// convert param names to Sort parameters
			std::vector<std::shared_ptr<Sort>> params;
			for(const auto& name : param_names) {
				params.push_back(sort_manager->createSort(name));
			}

			// get out sort
			std::shared_ptr<Sort> out_sort = parseSort();
			if(params.size() == 0){
				// it means an alias of the out sort
				sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(name, out_sort));
			}
			else{
				std::shared_ptr<Sort> sort = mkSortDef(name, params, out_sort);
				sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(name, sort));
			}
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
			in_quantifier_scope = true;
			quant_nesting_depth++;
			parseQuant("exists");
			quant_nesting_depth--;
			if(quant_nesting_depth == 0){
				in_quantifier_scope = false;
			}
			skipToRpar();
			return CMD_TYPE::CT_EXISTS;
		}
		if(command == "forall") {
			in_quantifier_scope = true;
			quant_nesting_depth++;
			parseQuant("forall");
			quant_nesting_depth--;
			if(quant_nesting_depth == 0){
				in_quantifier_scope = false;
			}
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

	// sort ::= <identifier> | (<identifier> <sort>+)
	std::shared_ptr<Sort> Parser::parseSort(){
		if(*bufptr == ')'){
			// all ready to return
			return SortManager::NULL_SORT;
		}
		// cache basic sorts
		static const std::unordered_map<std::string, std::shared_ptr<Sort>> BASIC_SORTS = {
			{"Bool", SortManager::BOOL_SORT}, 
			{"Int", SortManager::INT_SORT}, 
			{"Real", SortManager::REAL_SORT}, 
			{"RoundingMode", SortManager::ROUNDING_MODE_SORT},
			{"String", SortManager::STR_SORT}, 
			{"Float16", SortManager::FLOAT16_SORT}, 
			{"Float32", SortManager::FLOAT32_SORT}, 
			{"Float64", SortManager::FLOAT64_SORT},
			{"RegLan", SortManager::REG_SORT},
			{"Reg", SortManager::REG_SORT},
			{"RegEx", SortManager::REG_SORT}
		};
		
		if (*bufptr != '(') {
			// <identifier>
			size_t expr_ln = line_number;
			std::string s = getSymbol();

			// first check the basic type cache
			auto basic_it = BASIC_SORTS.find(s);
			if (basic_it != BASIC_SORTS.end()) {
				return basic_it->second;
			}
			// then check the user-defined type
			else if(sort_key_map.find(s) != sort_key_map.end()){
				return sort_key_map[s];
			}
			else err_unkwn_sym(s, expr_ln);
		}
		// (<identifier> <sort>+)
		// (_ <identifier> <param>+)
		parseLpar();
		size_t expr_ln = line_number;
		std::string s = getSymbol();

		//parse identifier and get params
		std::shared_ptr<Sort> sort = SortManager::NULL_SORT;
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
				sort = sort_manager->createArraySort(sortS, sortT);
				sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
			}
		}
		else if(s == "Datatype"){}
		else if(s == "Set"){}
		else if(s == "Relation"){}
		else if(s == "Bag"){}
		else if(s == "Sequence"){}
		else if(s == "RegEx"){
			// (RegEx <alphabet-sort>)
			std::shared_ptr<Sort> alphabet_sort = parseSort();
			if(!alphabet_sort->isStr()){
				err_all(ERROR_TYPE::ERR_TYPE_MIS, "RegEx sort expects String alphabet", expr_ln);
			}
			sort = SortManager::REG_SORT;
		}
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
					sort = sort_manager->createBVSort(std::stoi(n));
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
					sort = sort_manager->createFPSort(std::stoi(e), std::stoi(s));
					sort_key_map.insert(std::pair<std::string, std::shared_ptr<Sort>>(sort_key_name, sort));
				}
			}
			else err_unkwn_sym(s, expr_ln);
		}
		else {
			// first check the basic type cache
			auto basic_it = BASIC_SORTS.find(s);
			if (basic_it != BASIC_SORTS.end()) {
				sort = basic_it->second;
			}
			// then check the user-defined type
			else if(sort_key_map.find(s) != sort_key_map.end()){
				sort = sort_key_map[s];
			}
			else err_unkwn_sym(s, expr_ln);

			if (sort->arity > 0 ){
				for (size_t i = 0; i < sort->arity; i++){
					std::shared_ptr<Sort> sort_child = parseSort();
					if (sort_child->arity != sort_child->children.size())
						sort->children.push_back(sort_child);
				}
			}
		}
		//err_unkwn_sym(s, expr_ln);
		parseRpar();

		return sort;
	}

	std::vector<std::shared_ptr<DAGNode>> Parser::parseParams() {

		std::vector<std::shared_ptr<DAGNode>> params;

		while (*bufptr != ')'){
			std::shared_ptr<DAGNode> expr = parseExpr();
			params.emplace_back(expr);
		}

		return params;

	}

	// struct for let context
	struct LetContext {
		std::vector<std::shared_ptr<DAGNode>> params;  // let bind vars for current level
		std::vector<std::string> key_list;
		std::shared_ptr<DAGNode> result;  // Store the result directly
		std::shared_ptr<DAGNode> bind_var_list;  // LET_BIND_VAR_LIST for current level
		int nesting_level;
		bool is_complete;
		
		LetContext(int level = 0) : result(nullptr), bind_var_list(nullptr), nesting_level(level), is_complete(false) {}
	};

	// parse let expression preserving the let-binding
	// (let (<keybinding>+) expr), return expr
	// In this function, the let-binding is preserved, and the let-binding is not expanded
	// So the bind_var cannot be the same in different let-binding
	// For example, (let ((x 1) (x 2)) x) is not allowed
	// Use let-chain to parse the let expression
	// let-chain: [LET_BIND_VAR_LIST, LET_BIND_VAR_LIST, ..., Body]
	// LET_BIND_VAR_LIST: [(<symbol> expr)]
	// Body: expr
	std::shared_ptr<DAGNode> Parser::parsePreservingLet(){
		// This function uses an iterative approach instead of recursion to handle nested let expressions
		// and constructs let-chain to avoid deep nesting issues
		
		// Create a stack to store parsing states and contexts
		std::vector<LetContext> stateStack;
		
		// Collect all bind_var_lists for final let-chain construction
		std::vector<std::shared_ptr<DAGNode>> all_bind_var_lists;
		
		// Push initial state onto the stack
		stateStack.emplace_back(LetContext(0));
		
		// Enter the initial "("
		parseLpar();
		
		std::string preserving_let_bind_var_suffix = PRESERVING_LET_BIND_VAR_SUFFIX + std::to_string(preserving_let_counter);
		
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
					std::string prefixed_name = name + preserving_let_bind_var_suffix;
					
					// Check for duplicate key bindings
					if (preserving_let_key_map.find(prefixed_name) != preserving_let_key_map.end()) {
						// Clean up all variable bindings in the state stack
						for (auto &state : stateStack) {
							for (const auto &key : state.key_list) {
								preserving_let_key_map.erase(key);
							}
						}
						err_sym_mis("Duplicate variable binding: " + name, name_ln);
					}
					
					// Parse the expression value (this won't trigger recursive let parsing)
					std::shared_ptr<DAGNode> expr = parseExpr();
					
					if (expr->isErr()) {
						// Clean up all variable bindings in the state stack
						for (auto &state : stateStack) {
							for (const auto &key : state.key_list) {
								preserving_let_key_map.erase(key);
							}
						}
						err_all(expr, name, name_ln);
					}
					
				// make let-binding variable
				std::shared_ptr<DAGNode> let_var = mkLetBindVar(prefixed_name, expr);
				// Add the binding inside the mkLetBindVar
				// Add to params in the correct order - bindings first, body later
				params.emplace_back(let_var);
				key_list.emplace_back(prefixed_name);
				
				parseRpar();
			}
			
			// Create LET_BIND_VAR_LIST for current level and add to collection
			currentState.bind_var_list = mkLetBindVarList(params);
			all_bind_var_lists.emplace_back(currentState.bind_var_list);
			
			// Finished parsing all bindings for the current let, handle the closing parenthesis
			parseRpar();
		}
		
		// Process the body of the let expression
			if (*bufptr == '(' && peekSymbol() == "let") {
				// If the body is another let expression, we don't recursively call parseLet
				// Instead, push it as a new state onto the stack
				parseLpar();  // Consume '('
				std::string let_key = getSymbol();  // Consume "let"
				condAssert(let_key == "let", "Invalid keyword for let");
				parseLpar();  // Consume the second let expression's starting '('
				
				stateStack.emplace_back(LetContext(currentState.nesting_level + 1));
			}
			else{
				if(*bufptr != ')'){
					// Parse the let body and store as result
					currentState.result = parseExpr();
				}
				
				// State processing complete, pop from stack
				auto completedState = currentState;
				stateStack.pop_back();
				
				// If stack is empty, construct final let-chain and return
				if (stateStack.empty()) {
					// Create let-chain with all collected bind_var_lists + final body
					std::shared_ptr<DAGNode> result = mkLetChain(all_bind_var_lists, completedState.result);
					return result;
				}
				else{
					// Consume the closing parenthesis if needed
					parseRpar();
					
					// Pass the result to parent level (don't create let-chain yet)
					stateStack.back().result = completedState.result;
					stateStack.back().is_complete = true;
				}
			}
		}
		
		// Should not reach here, but added for safety  
		return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
	}
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
						err_sym_mis("Duplicate variable binding: " + name, name_ln);
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
				condAssert(let_key == "let", "Invalid keyword for let");
				parseLpar();  // Consume the second let expression's starting '('
				
				stateStack.emplace_back(LetContext(currentState.nesting_level + 1));
			}
			else{
				if(*bufptr != ')'){
					currentState.result = parseExpr();
				}
				
				// Remove all variable bindings for the current state
				for (const auto &key : key_list) {
					let_key_map.erase(key);
				}

				// State processing complete, pop from stack
				stateStack.pop_back();

				// If stack is empty, return the result directly
				if (stateStack.empty()) {
					return currentState.result;
				}
				else{
					// Consume the closing parenthesis
					parseRpar();
					// Store the result in the parent context
					stateStack.back().result = currentState.result;
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
			std::shared_ptr<DAGNode> result = node_manager->createNode(fun->getSort(), NODE_KIND::NT_UF_APPLY, fun->getName(), params);
			return result;
		}

	// For recursive functions (define-fun-rec), behavior depends on expand_recursive_functions option
	// If expand_recursive_functions is true, expand it like define-fun
	// If false (default), create a recursive function application node to avoid infinite recursion
	if(fun->isFuncRec()){
		if(!options->getExpandRecursiveFunctions()){
			// Don't expand recursive functions (default behavior)
			return mkApplyRecFunc(fun, params);
		}
		// Otherwise, fall through to expand it like define-fun
	}
	else if(fun->isFuncDec()){
		// a only declared function, i.e., uninterpreted function
		return mkApplyUF(fun->getSort(), fun->getName(), params);
	}

	// For regular functions (define-fun), check expand_functions option
	if(fun->isFuncDef()){
		if(!options->getExpandFunctions()){
			// Don't expand functions, create a function application node
			return mkApplyFunc(fun, params);
		}
		// Otherwise, fall through to expand the function
	}

	if(fun->getFuncBody()->isErr()){
		return fun->getFuncBody();
	}
	
	// Expand the function: replace parameters with actual arguments
	// variable map for local variables
	std::unordered_map<std::string, std::shared_ptr<DAGNode>> new_params_map;
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
	std::shared_ptr<DAGNode> Parser::applyFunPostOrder(std::shared_ptr<DAGNode> node, std::unordered_map<std::string, std::shared_ptr<DAGNode>> & params){
		if (!node) return nullptr;
		
		// Stack to track nodes to process
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		
		// Map to store processed results for each node
		std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> results;
		
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
				std::shared_ptr<DAGNode> result;
				if (current->isUFApplication()) {
					// NT_UF_APPLY: Must preserve function name when recreating node
					result = mkApplyUF(current->getSort(), current->getName(), childResults);
				} else if (current->isFuncRecApplication() && !options->getExpandRecursiveFunctions()) {
					// NT_FUNC_REC_APPLY: Recursive function call when not expanding
					// Must preserve function name when recreating node
					result = mkApplyRecFunc(current, childResults);
				} else if (current->isFuncApplication() || (current->isFuncRecApplication() && options->getExpandRecursiveFunctions())) {
					// NT_FUNC_APPLY or NT_FUNC_REC_APPLY (when expanding)
					// Parameters have been processed, now expand the function
					std::vector<std::shared_ptr<DAGNode>> funcParams;
					for (size_t i = 1; i < childResults.size(); i++) {
						funcParams.emplace_back(childResults[i]);
					}
					result = applyFun(current->getFuncBody(), funcParams);
				} else {
					// For all other cases: regular operators
					result = mkOper(current->getSort(), current->getKind(), childResults);
				}
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
				} else {
					// All other cases: operators, function applications, UF applications, etc.
					// Mark the node for revisit after processing children
					todo.push(std::make_pair(current, true));
					
					// For function applications that will be expanded, skip the first child (function definition itself)
					// For all other nodes, process all children
					bool isFuncAppToExpand = current->isFuncApplication() || 
					                        (current->isFuncRecApplication() && options->getExpandRecursiveFunctions());
					int startIdx = isFuncAppToExpand ? 1 : 0;
					
					// Push all children onto the stack in reverse order
					for (int i = current->getChildrenSize() - 1; i >= startIdx; i--) {
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

	
    std::shared_ptr<DAGNode> Parser::mkApplyRecFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params){
        // Create a recursive function application node (similar to mkApplyFunc)
        // Store function definition in children[0] and params in children[1..]
        std::shared_ptr<DAGNode> res = std::shared_ptr<DAGNode>(new DAGNode(fun->getSort(), NODE_KIND::NT_FUNC_REC_APPLY, fun->getName()));
        res->updateApplyFunc(fun->getSort(), fun, params, true);
        static_functions.emplace_back(res);
        return res;
    }

    std::shared_ptr<DAGNode> Parser::mkApplyUF(const std::shared_ptr<Sort>& sort, const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params){
        return node_manager->createNode(sort, NODE_KIND::NT_UF_APPLY, name, params);
    }


	// QUANTIFIERS
	// (quantifier ((<identifier> <sort>)+） <expr>)
	std::shared_ptr<DAGNode> Parser::mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort){
		if(quant_var_map.find(name) != quant_var_map.end()){
			return quant_var_map[name];
		}
		else{
			std::shared_ptr<DAGNode> var = node_manager->createNode(sort, NODE_KIND::NT_QUANT_VAR, name);
			quant_var_map.insert(std::pair<std::string, std::shared_ptr<DAGNode>>(name, var));
			return var;
		}
	}
	std::shared_ptr<DAGNode> Parser::parseQuant(const std::string& type){
		// (quantifier ((<identifier> <sort>)+） <expr>)
		//             ^
		parseLpar();
		std::vector<std::shared_ptr<DAGNode>> params;
		std::vector<std::string> quant_var_names;
		while (*bufptr != ')') {
			// (quantifier ((<identifier> <sort>)+） <expr>)
			//              ^
			parseLpar();
			std::string var_name = getSymbol();
			std::shared_ptr<Sort> var_sort = parseSort();
			std::shared_ptr<DAGNode> var = mkQuantVar(var_name, var_sort);
			params.emplace_back(var);
			quant_var_names.emplace_back(var_name);
			parseRpar();
		}
		// (quantifier ((<identifier> <sort>)+） <expr>)
		//                                    ^
		parseRpar();
		std::shared_ptr<DAGNode> body = parseExpr();
		params.insert(params.begin(), body);
		std::shared_ptr<DAGNode> res = NodeManager::NULL_NODE;
		if (type == "forall") {
			res = mkForall(params);
		}
		else if (type == "exists") {
			res = mkExists(params);
		}
		else{
			condAssert(false, "Invalid quantifier");
		}
		for(auto& name : quant_var_names){
			quant_var_map.erase(name);
		}
		return res;
	}

	std::shared_ptr<DAGNode> Parser::mkForall(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FORALL, params);
	}
	std::shared_ptr<DAGNode> Parser::mkExists(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_EXISTS, params);
	}

	
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params){
		std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
		return substitute(expr, params, visited);
	}
	// visited is used to avoid infinite loop
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited){
		/*
			Convert the previously recursive implementation into an iterative, stack-based
			post-order traversal to avoid potential stack-overflow on very deep/large DAGs.
			The algorithm mirrors the logic of applyFunPostOrder used elsewhere in this file.
		*/

		// Quick hit: if we already substituted this node, return the cached result.
		if(visited.find(expr) != visited.end()){
			return visited[expr];
		}

		// (node, processed?)  processed==false  => first time we see the node
		//                      processed==true   => all children have been handled
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		todo.push(std::make_pair(expr, false));

		while(!todo.empty()){
			auto curPair   = todo.top();
			todo.pop();
			std::shared_ptr<DAGNode> current = curPair.first;
			bool processed                  = curPair.second;

			// If we already computed a substitute for this node elsewhere, skip.
			if(visited.find(current) != visited.end()){
				continue;
			}

		if(processed){
			/*
				All children have been processed – build the new node using the
				(possibly substituted) child results that are now stored in
				`visited`.
			*/
			std::vector<std::shared_ptr<DAGNode>> newChildren;
			newChildren.reserve(current->getChildrenSize());
			for(size_t i = 0; i < current->getChildrenSize(); ++i){
				newChildren.emplace_back(visited[current->getChild(i)]);
			}
			std::shared_ptr<DAGNode> newNode;
			// For nodes with meaningful names (UF applications, function applications, etc.),
			// preserve the original name instead of using kindToString
			if(current->isUFApplication() || 
			   current->isFuncApplication() || 
			   current->isFuncRecApplication() ||
			   current->isArray()) {
				// Create node with original name preserved
				newNode = node_manager->createNode(current->getSort(), current->getKind(), current->getName(), newChildren);
			} else {
				// Use standard mkOper for other node types
				newNode = mkOper(current->getSort(), current->getKind(), newChildren);
			}
			visited[current] = newNode;
		}
			else{
				/* First visit */
				if(current->isVar()){
					// Variable: replace if it appears in the substitution map
					auto it = params.find(current->getName());
					visited[current] = (it != params.end()) ? it->second : current;
				}
				else if(current->isConst() || current->isFuncParam()){
					// Constants and function-parameters stay unchanged
					visited[current] = current;
				}
				else{
					// Non-leaf operator node – schedule a second visit after children
					todo.push(std::make_pair(current, true));
					// Push children (reverse order keeps original left-to-right after pop)
					for(int i = static_cast<int>(current->getChildrenSize()) - 1; i >= 0; --i){
						auto child = current->getChild(i);
						if(visited.find(child) == visited.end()){
							todo.push(std::make_pair(child, false));
						}
					}
				}
			}
		}

		return visited[expr];
	}

	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr){
		bool is_changed = false;
		return arithNormalize(expr, is_changed);
	}


	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr, bool& is_changed){
		// Iterative implementation to avoid stack overflow on very deep/large DAGs
		if(expr->isErr()){
			is_changed = false;
			return expr;
		}

		// Expand outer let expression (expandLet itself can still be recursive, but the overall depth is usually limited)
		if(expr->isLet()){
			expr = expandLet(expr);
		}

		// Use manual post-order traversal stack
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> result_map;   // Record normalized nodes
		std::unordered_map<std::shared_ptr<DAGNode>, bool>                     changed_map;  // Record if the node has changed

		todo.push({expr, false});

		while(!todo.empty()){
			auto [node, processed] = todo.top();
			todo.pop();

			// If already processed, skip
			if(result_map.find(node) != result_map.end()) continue;

		if(processed){
			/* Second visit: all children have been processed, can construct the current node */
			if(node->isConst() || node->isVar() || node->isArithTerm() || node->isErr()){
				result_map[node]  = node;
				changed_map[node] = false;
				continue;
			}

			if(node->isArithComp()){
				condAssert(node->getChildrenSize()==2, "ArithComp should have two children");
				std::shared_ptr<DAGNode> leftN  = result_map[node->getChild(0)];
				std::shared_ptr<DAGNode> rightN = result_map[node->getChild(1)];
				bool child_changed = changed_map[node->getChild(0)] || changed_map[node->getChild(1)];

				bool cur_changed = child_changed;
				std::shared_ptr<DAGNode> new_node = node; // default to keep unchanged

				if(!rightN->isConst()){
					cur_changed = true;
					auto left_sub = mkOper(leftN->getSort(), NODE_KIND::NT_SUB, {leftN, rightN});
					auto zero     = getZero(leftN->getSort());
					new_node      = mkOper(SortManager::BOOL_SORT, node->getKind(), {left_sub, zero});
				}else if(child_changed){
					new_node = mkOper(node->getSort(), node->getKind(), {leftN, rightN});
				}

				result_map[node]  = new_node;
				changed_map[node] = cur_changed;
				continue;
			}

			/* General operator */
			std::vector<std::shared_ptr<DAGNode>> new_children;
			bool any_changed = false;
			new_children.reserve(node->getChildrenSize());
			for(size_t i=0;i<node->getChildrenSize();++i){
				auto child = node->getChild(i);
				new_children.emplace_back(result_map[child]);
				any_changed = any_changed || changed_map[child];
			}

			std::shared_ptr<DAGNode> new_node;
			if(any_changed){
				// For nodes with meaningful names (UF applications, function applications, etc.),
				// preserve the original name instead of using kindToString
				if(	node->isUFApplication() || 
					node->isFuncApplication() || 
					node->isFuncRecApplication() ||
					node->isArray()) {
					// Create node with original name preserved
					new_node = node_manager->createNode(node->getSort(), node->getKind(), node->getName(), new_children);
				} else {
					// Use standard mkOper for other node types
					new_node = mkOper(node->getSort(), node->getKind(), new_children);
				}
			} else {
				new_node = node;
			}

			result_map[node]  = new_node;
			changed_map[node] = any_changed;
			}else{
				/* First visit */
				// Leaf node directly processed
				if(node->isConst() || node->isVar() || node->isArithTerm() || node->isErr()){
					result_map[node]  = node;
					changed_map[node] = false;
					continue;
				}

				// If it is still let, expand and push back to stack for processing
				if(node->isLet()){
					node = expandLet(node);
					todo.push({node, false});
					continue;
				}

				// Push back self (mark as visited), then push children
				todo.push({node, true});
				for(int i = static_cast<int>(node->getChildrenSize()) - 1; i >= 0; --i){
					todo.push({node->getChild(i), false});
				}
			}
		}

		is_changed = changed_map[expr];
		return result_map[expr];
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
		if(sort->isInt() || sort->isReal() || sort->isIntOrReal()){
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
	NODE_KIND Parser::getNegatedKind(NODE_KIND kind){
		return SMTParser::getNegatedKind(kind);
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

	// parse model
	ModelPtr Parser::parseModel(const std::string& model, bool only_declared){
		std::shared_ptr<Model> model_ptr = std::make_shared<Model>();
		
		// Save original parser state
		char* original_buffer = buffer;
		char* original_bufptr = bufptr;
		size_t original_buflen = buflen;
		bool original_parsing_file = parsing_file;
		
		// Set temporary parsing state
		parsing_file = false;
		buffer = safe_strdup(model);
		if (!buffer) {
			return model_ptr;
		}
		buflen = model.length();
		bufptr = buffer;
		scanToNextSymbol();
		
		try {
			// Check if wrapped with (model ...) or just (...)
			if (*bufptr == '(') {
				char* lookahead = bufptr + 1;
				while (*lookahead && (*lookahead == ' ' || *lookahead == '\t' || *lookahead == '\n' || *lookahead == '\r')) {
					lookahead++;
				}
				
				// Check if next symbol is "model"
				if (strncmp(lookahead, "model", 5) == 0 && 
				    (lookahead[5] == ' ' || lookahead[5] == '\t' || lookahead[5] == '\n' || lookahead[5] == '\r' || lookahead[5] == '(')) {
					// Skip outer (model ...)
					parseLpar();
					std::string keyword = getSymbol();
					// Now we're inside (model ...) or just (...), continue parsing define-fun
				} else {
					// Just a plain ( wrapping the define-funs, skip it
					parseLpar();
				}
			}
			
			// Parse all define-fun definitions
			while (*bufptr && *bufptr != 0) {
				// Skip whitespace
				while (*bufptr && (*bufptr == ' ' || *bufptr == '\t' || *bufptr == '\n' || *bufptr == '\r')) {
					bufptr++;
					if (*bufptr == '\n') line_number++;
				}
				
				if (*bufptr == 0 || *bufptr == ')') break;
				
				if (*bufptr != '(') break;
				
				// Parse one define-fun
				parseLpar();
				std::string keyword = getSymbol();
				
				if (keyword != "define-fun") {
					// Not a define-fun, skip it
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Parse variable name (can be any symbol including | | or ||)
				// Note: In SMT-LIB, | | means a symbol containing a space, || means an empty symbol
				std::string var_name;
				
				// Check if next token is a parameter list instead of a name
				if (*bufptr == '(') {
					// No variable name provided, treat it as empty symbol ||
					var_name = "||"; // "" -> "||"
				} else {
					var_name = getSymbol();
				}
				
				// Parse parameter list
				parseLpar();
				bool has_params = (*bufptr != ')');
				
				// Skip parameters
				while (*bufptr != ')') {
					parseLpar();
					getSymbol(); // parameter name
					parseSort(); // parameter type
					parseRpar();
				}
				parseRpar();
				
				// If has parameters, skip this function definition
				if (has_params) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Parse type
				std::shared_ptr<Sort> var_sort = parseSort();
				if (!var_sort) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Check if only declared variables
				if (only_declared && !isDeclaredVariable(var_name)) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Define variable first
				std::shared_ptr<DAGNode> var_node = mkVar(var_sort, var_name);
				
				// Parse value expression
				std::shared_ptr<DAGNode> value = parseExpr();
				
				if (value && !value->isErr()) {
					model_ptr->add(var_node, value);
				}
				
				// Close the define-fun
				parseRpar();
			}
			
		} catch (...) {
			// Ignore errors and return what we have
		}
		
		// Restore original state
		delete[] buffer;
		buffer = original_buffer;
		bufptr = original_bufptr;
		buflen = original_buflen;
		parsing_file = original_parsing_file;
		
		return model_ptr;
	}

	ModelPtr Parser::newEmptyModel(){
		// new empty model
		std::shared_ptr<Model> model = std::make_shared<Model>();
		// get all variables
		std::vector<std::shared_ptr<DAGNode>> vars = getDeclaredVariables();
		for(auto& var : vars){
			model->addVar(var);
		}
		return model;
	}

	bool Parser::isDeclaredVariable(const std::string& var_name) const{
		return var_names.find(var_name) != var_names.end();
	}
	bool Parser::isDeclaredFunction(const std::string& func_name) const{
		return fun_key_map.find(func_name) != fun_key_map.end();
	}


	// error operations
	std::shared_ptr<DAGNode> Parser::mkErr(const ERROR_TYPE t){
		return node_manager->createNode(NODE_KIND::NT_ERROR);
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
		condAssert(expr->isVar(), "Only variable can be renamed");
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

	std::string Parser::optionToString(){
		return options->toString();
	}

	std::string Parser::dumpSMT2(){
		std::stringstream ss;
		ss << "(set-logic " << options->getLogic() << ")" << std::endl;
		// custom sorts
		for(auto& sort_pair : sort_key_map){
			if(sort_pair.second->isDec()){
				ss << "(declare-sort " << sort_pair.first << " " << sort_pair.second->arity << ")" << std::endl;
			}
		}
		// variables
		std::vector<std::shared_ptr<DAGNode>> vars = getVariables();
		for(auto& var : vars){
			ss << "(declare-fun " << var->getName() << " () " << var->getSort()->toString() << ")" << std::endl;
		}
	std::vector<std::shared_ptr<DAGNode>> functions = getFunctions();
	for(auto& func : functions){
		if(func->isFuncDec()){
			// NT_FUNC_DEC: Uninterpreted function declaration (declare-fun)
			ss << dumpFuncDec(func) << std::endl;
		}
		else if(func->isFuncRec()){
			// NT_FUNC_REC: Recursive function definition (define-fun-rec)
			ss << dumpFuncRec(func) << std::endl;
		}
		else{
			// NT_FUNC_DEF: Regular function definition (define-fun)
			ss << dumpFuncDef(func) << std::endl;
		}
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

	size_t Parser::removeFuns(const std::vector<std::string>& funcNames){
		size_t removedCount = 0;
		
		for(const auto& funcName : funcNames){
			// Check if function exists in fun_key_map
			auto funIt = fun_key_map.find(funcName);
			if(funIt != fun_key_map.end()){
				// Remove from fun_key_map
				fun_key_map.erase(funIt);
				removedCount++;
				
				// Remove from function_names vector
				auto nameIt = std::find(function_names.begin(), function_names.end(), funcName);
				if(nameIt != function_names.end()){
					function_names.erase(nameIt);
				}
			}
		}
		
		return removedCount;
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
