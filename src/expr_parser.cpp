/* -*- Source -*-
 *
 * An SMT/OMT Parser (Expression part)
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

namespace SMTParser{
    // State of the parser
    enum class FrameState {
        Start,
        ProcessingArgs,
        Finish
    };

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
    // Frame of the parser
    struct ParseFrame {
        FrameState state;
        std::string headSymbol;  // symbol of the head of the frame
        std::vector<std::shared_ptr<DAGNode>> args;
        size_t argIndex = 0;     // index of the current argument
        int line;                // line number of the frame
        LetContext let_context;  // let context of the frame
    };
    
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
			if(s == "exists"){
				expr = parseQuant("exists");
			}
			else if(s == "forall"){
				expr = parseQuant("forall");
			}
			//parse identifier and get params
			else if(s == "_"){
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
				// LET Mode - use nesting depth to track let state
				if(let_nesting_depth == 0){
					// Entering the outermost let
					current_let_mode = LET_MODE::LM_START_LET;
					preserving_let_counter += 1;
				}
				else if(current_let_mode == LET_MODE::LM_START_LET){
					current_let_mode = LET_MODE::LM_IN_LET;
				}
				// Increment nesting depth for any let
				let_nesting_depth++;

				if(options->parsing_preserve_let){
					expr = parsePreservingLet();
				}
				else{
					expr = parseLet();
				}
				
				// Decrement nesting depth when let parsing is complete
				let_nesting_depth--;
				
				// Only reset let mode when completely out of all lets
				if(let_nesting_depth == 0){
					current_let_mode = LET_MODE::LM_NON_LET;
				}
				
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

    std::shared_ptr<DAGNode> Parser::parseExprIterative() {
        std::stack<ParseFrame> callStack;
        std::stack<std::shared_ptr<DAGNode>> resultStack;
    
        while (true) {
            if (*bufptr != '(') {
                //const | func
                // handle const or func with no args
                size_t expr_ln = line_number;
                std::string s = getSymbol();
    
                std::shared_ptr<DAGNode> expr = parseConstFunc(s);
                if(expr->isErr()) err_unkwn_sym(s, expr_ln);
                resultStack.push(expr);
                if (callStack.empty()) break;
                continue;
            }
    
            // start of a compound expression
		    parseLpar();
    
            std::string head = getSymbol();  // e.g. and, +, let, exists, etc.
            ParseFrame frame;
            frame.state = FrameState::ProcessingArgs;
            frame.headSymbol = head;
            frame.line = line_number;
            callStack.push(frame);
    
            // continue to read arguments
            while (!callStack.empty()) {
                ParseFrame& top = callStack.top();
                if (top.state == FrameState::ProcessingArgs) {
                    skipWhitespace();
                    if (*bufptr == ')') {
                        parseRpar(); // consume ')'
                        auto node = makeNode(top.headSymbol, top.args);
                        callStack.pop();
                        resultStack.push(node);
                        continue;
                    }
    
                    // otherwise, read a sub-expression
                    top.state = FrameState::ProcessingArgs;
                    callStack.push(ParseFrame{FrameState::Start});  // new expr sub-item
                    break;  // enter the next round of processing
                } else if (top.state == FrameState::Start) {
                    // get the just processed sub-expression from resultStack
                    auto arg = resultStack.top(); resultStack.pop();
                    callStack.pop();
                    callStack.top().args.push_back(arg);  // push to the upper frame
                }
            }
    
            if (callStack.empty()) break;
        }
    
        return resultStack.top();
    }

	
	std::shared_ptr<DAGNode> Parser::parseConstFunc(const std::string& s){
		// first handle the special symbols
		if (s == "true") {
			return mkTrue();
		}
		else if (s == "false") {
			return mkFalse();
		}
		
		// these have the highest priority
		std::string preserving_let_name = s + PRESERVING_LET_BIND_VAR_SUFFIX + std::to_string(preserving_let_counter);
		if(options->parsing_preserve_let && current_let_mode != LET_MODE::LM_NON_LET && preserving_let_key_map.find(preserving_let_name) != preserving_let_key_map.end()){
			return preserving_let_key_map[preserving_let_name];
		}
		else if(!options->parsing_preserve_let && current_let_mode != LET_MODE::LM_NON_LET && let_key_map.find(s) != let_key_map.end()){
			return let_key_map[s];
		}
		else if(let_key_map.find(s) != let_key_map.end()){
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
			return node_manager->getNode(var_names[s]);
		}
		else if(quant_var_map.find(s) != quant_var_map.end()){
			// quantifier variable name
			return quant_var_map[s];
		}
		// following Common Lisp's conventions, enclosing
		// a simple symbol in vertical bars does not produce a new symbol.
		else if(s.size() > 2 && 
				s[0] == '|'  && 
				s[s.size() - 1] == '|' &&
				var_names.find(s.substr(1, s.size() - 2)) != var_names.end()){
			// string
			return node_manager->getNode(var_names[s.substr(1, s.size() - 2)]);
		}
		else if(!TypeChecker::isNumber(s) && 
				var_names.find('|' + s + '|') != var_names.end()){
			// string
			return node_manager->getNode(var_names['|' + s + '|']);
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
		else if(TypeChecker::isInt(s)){
			// additional process -> constant can be real or integer
			// 0 -> Int or Real?
			return mkConstInt(s);
		}
		else if(TypeChecker::isReal(s)){
			return mkConstReal(s);
		}
		else if(TypeChecker::isScientificNotation(s)){
			// parse scientific notation and convert to real
			std::string parsed = ConversionUtils::parseScientificNotation(s);
			return mkConstReal(parsed);
		}
		else if(TypeChecker::isBV(s)){
			return mkConstBv(s, s.size() - 2);
		}
		// else if(TypeChecker::isFP(s)){
		// 	return mkConstFP(s);
		// }
		else if(TypeChecker::isString(s)){
			return mkConstStr(s);
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
			err_unkwn_sym(s, line_number);
		}
		return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
	}
}