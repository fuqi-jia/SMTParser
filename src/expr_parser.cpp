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
#include "parser.h"
#include <stack>

namespace SMTParser{
    // State of the parser
    enum class FrameState {
        Start,
        ReadingHead,           // reading head symbol
        ProcessingArgs,        // processing normal arguments
        ProcessingSpecial,     // processing special syntax
        ProcessingParams,      // processing parameter list
        ProcessingBindings,    // processing let bindings
        ProcessingLetBody,     // processing let body
        ProcessingQuantVars,   // processing quantifier variables
        ProcessingQuantBody,   // processing quantifier body
        ProcessingParamFuncArgs, // processing parameter function arguments
        ProcessingParamFuncParams, // processing parameter function parameters
        Finish
    };

    // special processing type
    enum class SpecialType {
        None,
        Let,
        Exists,
        Forall,
        ParamFunc,
        BV,
        Underscore
    };

    // Frame of the parser (精简版)
    struct ExprFrame {
        FrameState state = FrameState::Start;
        SpecialType special_type = SpecialType::None;
        std::string headSymbol;                      // 头符号
        std::string second_symbol;                   // "(_ f …)" 里的 f
        std::vector<std::shared_ptr<DAGNode>> args;  // 普通实参
        std::vector<std::shared_ptr<DAGNode>> params;// 参数化函数的参数
        int line = 0;                                // 行号
        std::shared_ptr<DAGNode> result;             // 解析结果

        ExprFrame() = default;
    };
    
	// expr ::= const | func | (<identifier> <expr>+)
	std::shared_ptr<DAGNode> Parser::parseExpr() {
        std::stack<ExprFrame> st;
        st.push(ExprFrame());

        while(!st.empty()){
            ExprFrame &frame = st.top();

            switch(frame.state){
                case FrameState::Start:{
                    // 处理最简单的符号或常量
                    if(*bufptr != '('){
                        size_t ln = line_number;
                        std::string sym = getSymbol();
                        auto node = parseConstFunc(sym);
                        if(node->isErr()) err_unkwn_sym(sym, ln);
                        frame.result = node;
                        frame.state = FrameState::Finish;
                        break;
                    }

                    // 复合表达式
                    parseLpar();
                    frame.line = line_number;

                    // 检查 ((_ f args) ...) 这种形式
                    if(*bufptr == '('){
                        parseLpar();
                        std::string s = getSymbol();
                        if(s != "_"){
                            err_unkwn_sym(s, frame.line);
                            frame.result = mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
                            frame.state = FrameState::Finish;
                            break;
                        }
                        frame.special_type = SpecialType::ParamFunc;
                        frame.second_symbol = getSymbol();
                        frame.state = FrameState::ProcessingParamFuncArgs;
                        break;
                    }

                    // 读取头部符号
                    std::string head = getSymbol();
                    frame.headSymbol = head;

                    if(head == "exists" || head == "forall"){
                        auto res = parseQuant(head);
                        parseRpar();
                        frame.result = res;
                        frame.state = FrameState::Finish;
                    }
                    else if(head == "_"){
                        std::string second = getSymbol();
                        if(second.size() >= 2 && second[0]=='b' && second[1]=='v'){
                            std::string width_str = getSymbol();
                            size_t width = std::stoul(width_str);
                            std::string num = second.substr(2);
                            frame.result = mkConstBv(num, width);
                            parseRpar();
                            frame.state = FrameState::Finish;
                        }else{
                            frame.second_symbol = second;
                            frame.state = FrameState::ProcessingArgs;
                        }
                    }
                    else if(head == "let"){
                        if(let_nesting_depth == 0){
                            current_let_mode = LET_MODE::LM_START_LET;
                            preserving_let_counter += 1;
                        }else if(current_let_mode == LET_MODE::LM_START_LET){
                            current_let_mode = LET_MODE::LM_IN_LET;
                        }
                        let_nesting_depth++;

                        std::shared_ptr<DAGNode> res;
                        if(options->parsing_preserve_let){
                            res = parsePreservingLet();
                        }else{
                            res = parseLet();
                        }

                        let_nesting_depth--;
                        if(let_nesting_depth == 0){
                            current_let_mode = LET_MODE::LM_NON_LET;
                        }

                        if(res->isErr()) err_all(res, "let", frame.line);
                        parseRpar();
                        frame.result = res;
                        frame.state = FrameState::Finish;
                    }
                    else{
                        frame.state = FrameState::ProcessingArgs;
                    }
                    break;
                }

                case FrameState::ProcessingArgs:{
                    skipToRpar();
                    if(*bufptr == ')'){
                        parseRpar();
                        std::shared_ptr<DAGNode> res;
                        if(frame.headSymbol == "_"){
                            res = parseOper(frame.second_symbol, frame.args);
                        }else{
                            res = parseOper(frame.headSymbol, frame.args);
                        }
                        if(res->isErr()) err_all(res, frame.headSymbol, frame.line);
                        frame.result = res;
                        frame.state = FrameState::Finish;
                        break;
                    }
                    st.push(ExprFrame());
                    break;
                }

                case FrameState::ProcessingParamFuncArgs:{
                    skipToRpar();
                    if(*bufptr == ')'){
                        parseRpar();
                        frame.state = FrameState::ProcessingParamFuncParams;
                        break;
                    }
                    st.push(ExprFrame());
                    break;
                }

                case FrameState::ProcessingParamFuncParams:{
                    skipToRpar();
                    if(*bufptr == ')'){
                        parseRpar();
                        auto res = parseParamFunc(frame.second_symbol, frame.args, frame.params);
                        if(!res || res->isErr()) err_unkwn_sym(frame.second_symbol, frame.line);
                        frame.result = res;
                        frame.state = FrameState::Finish;
                        break;
                    }
                    st.push(ExprFrame());
                    break;
                }

                case FrameState::Finish:{
                    auto res = frame.result;
                    st.pop();
                    if(st.empty()) return res;
                    ExprFrame &parent = st.top();
                    if(parent.state == FrameState::ProcessingArgs){
                        parent.args.push_back(res);
                    }else if(parent.state == FrameState::ProcessingParamFuncArgs){
                        parent.args.push_back(res);
                    }else if(parent.state == FrameState::ProcessingParamFuncParams){
                        parent.params.push_back(res);
                    }
                    break;
                }
                default:{
                    st.pop();
                    break;
                }
            }
        }

        return mkErr(ERROR_TYPE::ERR_UNKWN_SYM); // cannot reach here
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