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
#include "timing.h"
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
        TIME_FUNC();
        std::stack<ExprFrame> st;
        st.push(ExprFrame());

        while(!st.empty()){
            ExprFrame &frame = st.top();

            switch(frame.state){
                case FrameState::Start:{
                    // handle the simplest symbol or constant
                    if(*bufptr != '('){
                        size_t ln = line_number;
                        std::string sym = getSymbol();
                        auto node = parseConstFunc(sym);
                        if(node->isErr()) err_unkwn_sym(sym, ln);
                        frame.result = node;
                        frame.state = FrameState::Finish;
                        break;
                    }

                    // complex expression
                    parseLpar();
                    frame.line = line_number;

                    // check ((_ f args) ...)
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

                    // read the head symbol
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
                    // escape the space and comment
                    scanToNextSymbol();
                    if(*bufptr == ')'){
                        parseRpar();
                        std::shared_ptr<DAGNode> res;
                        if(frame.headSymbol == "_"){
                            res = parseOper(frame.second_symbol, {}, frame.args);
                        }else{
                            res = parseOper(frame.headSymbol, {}, frame.args);
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
                    // escape the space and comment
                    scanToNextSymbol();
                    if(*bufptr == ')'){
                        parseRpar();
                        frame.state = FrameState::ProcessingParamFuncParams;
                        break;
                    }
                    st.push(ExprFrame());
                    break;
                }

                case FrameState::ProcessingParamFuncParams:{
                    // escape the space and comment
                    scanToNextSymbol();
                    if(*bufptr == ')'){
                        parseRpar();
                        auto res = parseOper(frame.second_symbol, frame.args, frame.params);
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

    NODE_KIND Parser::getKind(const std::string& s){
        auto kind = SMTParser::getOperKind(s);
        if(kind == NODE_KIND::NT_UNKNOWN && fun_key_map.find(s) != fun_key_map.end()){
            kind = NODE_KIND::NT_FUNC_APPLY;
        }
        return kind;
    }
    
	std::shared_ptr<DAGNode> Parser::parseOper(const std::string& s, const std::vector<std::shared_ptr<DAGNode>>& args, const std::vector<std::shared_ptr<DAGNode>> &params){
		TIME_FUNC();
		auto kind = SMTParser::getOperKind(s);
		switch(kind){
			case NODE_KIND::NT_AND:
				return mkAnd(params);
			case NODE_KIND::NT_OR:
				return mkOr(params);
			case NODE_KIND::NT_NOT:
				condAssert(params.size() == 1, "Invalid number of parameters for not");
				return mkNot(params[0]);
			case NODE_KIND::NT_IMPLIES:
				return mkImplies(params);
			case NODE_KIND::NT_XOR:
				return mkXor(params);
			case NODE_KIND::NT_EQ:
				return mkEq(params);
			case NODE_KIND::NT_DISTINCT:
				return mkDistinct(params);
			case NODE_KIND::NT_ITE:
				return mkIte(params);
			case NODE_KIND::NT_ADD:
				return mkAdd(params);
            case NODE_KIND::NT_NEG:
                condAssert(params.size() == 1, "Invalid number of parameters for neg");
                return mkNeg(params[0]);
			case NODE_KIND::NT_SUB:
				return mkSub(params);
			case NODE_KIND::NT_MUL:
				return mkMul(params);
			case NODE_KIND::NT_IAND:
				return mkIand(params);
			case NODE_KIND::NT_POW2:
				condAssert(params.size() == 1, "Invalid number of parameters for pow2");
				return mkPow2(params[0]);
			case NODE_KIND::NT_POW:
				condAssert(params.size() == 2, "Invalid number of parameters for pow");
				return mkPow(params[0], params[1]);
			case NODE_KIND::NT_DIV_INT:
				condAssert(params.size() == 2, "Invalid number of parameters for div");
				return mkDivInt(params[0], params[1]);
			case NODE_KIND::NT_DIV_REAL:
				condAssert(params.size() == 2, "Invalid number of parameters for div");
				return mkDivReal(params[0], params[1]);
			case NODE_KIND::NT_MOD:
				condAssert(params.size() == 2, "Invalid number of parameters for mod");
				return mkMod(params[0], params[1]);
			case NODE_KIND::NT_ABS:
				condAssert(params.size() == 1, "Invalid number of parameters for abs");
				return mkAbs(params[0]);
			case NODE_KIND::NT_SQRT:
				condAssert(params.size() == 1, "Invalid number of parameters for sqrt");
				return mkSqrt(params[0]);
			case NODE_KIND::NT_SAFESQRT:
				condAssert(params.size() == 1, "Invalid number of parameters for safeSqrt");
				return mkSafeSqrt(params[0]);
			case NODE_KIND::NT_CEIL:
				condAssert(params.size() == 1, "Invalid number of parameters for ceil");
				return mkCeil(params[0]);
			case NODE_KIND::NT_FLOOR:
				condAssert(params.size() == 1, "Invalid number of parameters for floor");
				return mkFloor(params[0]);
			case NODE_KIND::NT_ROUND:
				condAssert(params.size() == 1, "Invalid number of parameters for round");
				return mkRound(params[0]);
			case NODE_KIND::NT_EXP:
				condAssert(params.size() == 1, "Invalid number of parameters for exp");
				return mkExp(params[0]);
			case NODE_KIND::NT_LN:
				condAssert(params.size() == 1, "Invalid number of parameters for ln");
				return mkLn(params[0]);
			case NODE_KIND::NT_LG:
				condAssert(params.size() == 1, "Invalid number of parameters for lg");
				return mkLg(params[0]);
			case NODE_KIND::NT_LB:
				condAssert(params.size() == 1, "Invalid number of parameters for lb");
				return mkLb(params[0]);
			case NODE_KIND::NT_LOG:
				if(params.size() == 1){
					return mkLn(params[0]);
				}
				else if(params.size() == 2){
					return mkLog(params[0], params[1]);
				}
				else {
					err_param_mis("log", line_number);
					return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
				}
			case NODE_KIND::NT_SIN:
				condAssert(params.size() == 1, "Invalid number of parameters for sin");
				return mkSin(params[0]);
			case NODE_KIND::NT_COS:
				condAssert(params.size() == 1, "Invalid number of parameters for cos");
				return mkCos(params[0]);
			case NODE_KIND::NT_TAN:
				condAssert(params.size() == 1, "Invalid number of parameters for tan");
				return mkTan(params[0]);
			case NODE_KIND::NT_COT:
				condAssert(params.size() == 1, "Invalid number of parameters for cot");
				return mkCot(params[0]);
			case NODE_KIND::NT_SEC:
				condAssert(params.size() == 1, "Invalid number of parameters for sec");
				return mkSec(params[0]);
			case NODE_KIND::NT_CSC:
				condAssert(params.size() == 1, "Invalid number of parameters for csc");
				return mkCsc(params[0]);
			case NODE_KIND::NT_ASIN:
				condAssert(params.size() == 1, "Invalid number of parameters for asin");
				return mkAsin(params[0]);
			case NODE_KIND::NT_ACOS:
				condAssert(params.size() == 1, "Invalid number of parameters for acos");
				return mkAcos(params[0]);
			case NODE_KIND::NT_ATAN:
				condAssert(params.size() == 1, "Invalid number of parameters for atan");
				return mkAtan(params[0]);
			case NODE_KIND::NT_ACOT:
				condAssert(params.size() == 1, "Invalid number of parameters for acot");
				return mkAcot(params[0]);
			case NODE_KIND::NT_ASEC:
				condAssert(params.size() == 1, "Invalid number of parameters for asec");
				return mkAsec(params[0]);
			case NODE_KIND::NT_ACSC:
				condAssert(params.size() == 1, "Invalid number of parameters for acsc");
				return mkAcsc(params[0]);
			case NODE_KIND::NT_SINH:
				condAssert(params.size() == 1, "Invalid number of parameters for sinh");
				return mkSinh(params[0]);
			case NODE_KIND::NT_COSH:
				condAssert(params.size() == 1, "Invalid number of parameters for cosh");
				return mkCosh(params[0]);
			case NODE_KIND::NT_TANH:
				condAssert(params.size() == 1, "Invalid number of parameters for tanh");
				return mkTanh(params[0]);
			case NODE_KIND::NT_ASECH:
				condAssert(params.size() == 1, "Invalid number of parameters for asech");
				return mkAsech(params[0]);
			case NODE_KIND::NT_ACSCH:
				condAssert(params.size() == 1, "Invalid number of parameters for acsch");
				return mkAcsch(params[0]);
			case NODE_KIND::NT_ACOTH:
				condAssert(params.size() == 1, "Invalid number of parameters for acoth");
				return mkAcoth(params[0]);
			case NODE_KIND::NT_ATAN2:
				condAssert(params.size() == 2, "Invalid number of parameters for atan2");
				return mkAtan2(params[0], params[1]);
			case NODE_KIND::NT_ASINH:
				condAssert(params.size() == 1, "Invalid number of parameters for asinh");
				return mkAsinh(params[0]);
			case NODE_KIND::NT_ACOSH:
				condAssert(params.size() == 1, "Invalid number of parameters for acosh");
				return mkAcosh(params[0]);
			case NODE_KIND::NT_ATANH:
				condAssert(params.size() == 1, "Invalid number of parameters for atanh");
				return mkAtanh(params[0]);
            case NODE_KIND::NT_SECH:
                condAssert(params.size() == 1, "Invalid number of parameters for sech");
                return mkSech(params[0]);
            case NODE_KIND::NT_CSCH:
                condAssert(params.size() == 1, "Invalid number of parameters for csch");
                return mkCsch(params[0]);
            case NODE_KIND::NT_LE:
				condAssert(params.size() == 2, "Invalid number of parameters for <= ");
				return mkLe(params[0], params[1]);
			case NODE_KIND::NT_LT:
				condAssert(params.size() == 2, "Invalid number of parameters for <");
				return mkLt(params[0], params[1]);
			case NODE_KIND::NT_GE:
				condAssert(params.size() == 2, "Invalid number of parameters for >= ");
				return mkGe(params[0], params[1]);
			case NODE_KIND::NT_GT:
				condAssert(params.size() == 2, "Invalid number of parameters for >");
				return mkGt(params[0], params[1]);
			case NODE_KIND::NT_TO_REAL:
				condAssert(params.size() == 1, "Invalid number of parameters for to_real");
				return mkToReal(params[0]);
			case NODE_KIND::NT_TO_INT:
				condAssert(params.size() == 1, "Invalid number of parameters for to_int");
				return mkToInt(params[0]);
			case NODE_KIND::NT_IS_INT:
				condAssert(params.size() == 1, "Invalid number of parameters for is_int");
				return mkIsInt(params[0]);
			case NODE_KIND::NT_IS_DIVISIBLE:
				condAssert(params.size() == 2, "Invalid number of parameters for is_divisible");
				return mkIsDivisible(params[0], params[1]);
			case NODE_KIND::NT_IS_PRIME:
				condAssert(params.size() == 1, "Invalid number of parameters for is_prime");
				return mkIsPrime(params[0]);
			case NODE_KIND::NT_IS_EVEN:
				condAssert(params.size() == 1, "Invalid number of parameters for is_even");
				return mkIsEven(params[0]);
			case NODE_KIND::NT_IS_ODD:
				condAssert(params.size() == 1, "Invalid number of parameters for is_odd");
				return mkIsOdd(params[0]);
			case NODE_KIND::NT_GCD:
				condAssert(params.size() == 2, "Invalid number of parameters for gcd");
				return mkGcd(params[0], params[1]);
			case NODE_KIND::NT_LCM:
				condAssert(params.size() == 2, "Invalid number of parameters for lcm");
				return mkLcm(params[0], params[1]);
			case NODE_KIND::NT_FACT:
				condAssert(params.size() == 1, "Invalid number of parameters for factorial");
				return mkFact(params[0]);
			case NODE_KIND::NT_BV_NOT:
				condAssert(params.size() == 1, "Invalid number of parameters for bvnot");
				return mkBvNot(params[0]);
			case NODE_KIND::NT_BV_NEG:
				condAssert(params.size() == 1, "Invalid number of parameters for bvneg");
				return mkBvNeg(params[0]);
			case NODE_KIND::NT_BV_AND:
				return mkBvAnd(params);
			case NODE_KIND::NT_BV_OR:
				return mkBvOr(params);
			case NODE_KIND::NT_BV_XOR:
				return mkBvXor(params);
			case NODE_KIND::NT_BV_NAND:
				return mkBvNand(params);
			case NODE_KIND::NT_BV_NOR:
				return mkBvNor(params);
			case NODE_KIND::NT_BV_XNOR:
				return mkBvXnor(params);
			case NODE_KIND::NT_BV_COMP:
				condAssert(params.size() == 2, "Invalid number of parameters for bvcomp");
				return mkBvComp(params[0], params[1]);
			case NODE_KIND::NT_BV_ADD:
				return mkBvAdd(params);
			case NODE_KIND::NT_BV_SUB:
				return mkBvSub(params);
			case NODE_KIND::NT_BV_MUL:
				return mkBvMul(params);
			case NODE_KIND::NT_BV_UDIV:
				condAssert(params.size() == 2, "Invalid number of parameters for bvudiv");
				return mkBvUdiv(params[0], params[1]);
			case NODE_KIND::NT_BV_UREM:
				condAssert(params.size() == 2, "Invalid number of parameters for bvurem");
				return mkBvUrem(params[0], params[1]);
			case NODE_KIND::NT_BV_SDIV:
				condAssert(params.size() == 2, "Invalid number of parameters for bvsdiv");
				return mkBvSdiv(params[0], params[1]);
			case NODE_KIND::NT_BV_SREM:
				condAssert(params.size() == 2, "Invalid number of parameters for bvsmod");
				return mkBvSmod(params[0], params[1]);
			case NODE_KIND::NT_BV_SHL:
				condAssert(params.size() == 2, "Invalid number of parameters for bvshl");
				return mkBvShl(params[0], params[1]);
            case NODE_KIND::NT_BV_LSHR:
                condAssert(params.size() == 2, "Invalid number of parameters for bvlshr");
                return mkBvLshr(params[0], params[1]);
			case NODE_KIND::NT_BV_ASHR:
				condAssert(params.size() == 2, "Invalid number of parameters for bvashr");
				return mkBvAshr(params[0], params[1]);
            case NODE_KIND::NT_BV_ULT:
                condAssert(params.size() == 2, "Invalid number of parameters for bvult");
                return mkBvUlt(params[0], params[1]);
            case NODE_KIND::NT_BV_ULE:
                condAssert(params.size() == 2, "Invalid number of parameters for bvule");
                return mkBvUle(params[0], params[1]);
            case NODE_KIND::NT_BV_UGT:
                condAssert(params.size() == 2, "Invalid number of parameters for bvugt");
                return mkBvUgt(params[0], params[1]);
            case NODE_KIND::NT_BV_UGE:
                condAssert(params.size() == 2, "Invalid number of parameters for bvuge");
                return mkBvUge(params[0], params[1]);
            case NODE_KIND::NT_BV_SLT:
                condAssert(params.size() == 2, "Invalid number of parameters for bvslt");
                return mkBvSlt(params[0], params[1]);
            case NODE_KIND::NT_BV_SLE:
                condAssert(params.size() == 2, "Invalid number of parameters for bvsle");
                return mkBvSle(params[0], params[1]);
            case NODE_KIND::NT_BV_SGT:
                condAssert(params.size() == 2, "Invalid number of parameters for bvsgt");
                return mkBvSgt(params[0], params[1]);
            case NODE_KIND::NT_BV_SGE:
                condAssert(params.size() == 2, "Invalid number of parameters for bvsge");
                return mkBvSge(params[0], params[1]);
            case NODE_KIND::NT_BV_CONCAT:
				return mkBvConcat(params);
            case NODE_KIND::NT_BV_TO_INT:
                condAssert(params.size() == 1, "Invalid number of parameters for bv2int");
                return mkBvToInt(params[0]);
            case NODE_KIND::NT_BV_TO_NAT:
                condAssert(params.size() == 1, "Invalid number of parameters for bv2nat");
                return mkBvToNat(params[0]);
            case NODE_KIND::NT_NAT_TO_BV:
                condAssert(params.size() == 2, "Invalid number of parameters for nat2bv");
                return mkNatToBv(params[0], params[1]);
            case NODE_KIND::NT_INT_TO_BV:
                condAssert(args.size() == 1, "Invalid number of arguments for int_to_bv");
                condAssert(params.size() == 1, "Invalid number of parameters for int_to_bv");
                return mkIntToBv(params[0], args[0]);
            case NODE_KIND::NT_BV_EXTRACT:
                condAssert(args.size() == 2, "Invalid number of arguments for extract");
                condAssert(params.size() == 1, "Invalid number of parameters for extract");
                return mkBvExtract(params[0], args[0], args[1]);
            case NODE_KIND::NT_BV_REPEAT:
                condAssert(args.size() == 1, "Invalid number of arguments for repeat");
                condAssert(params.size() == 1, "Invalid number of parameters for repeat");
                return mkBvRepeat(params[0], args[0]);
            case NODE_KIND::NT_BV_ZERO_EXT:
                condAssert(args.size() == 1, "Invalid number of arguments for zero_extend");
                condAssert(params.size() == 1, "Invalid number of parameters for zero_extend");
                return mkBvZeroExt(params[0], args[0]);
            case NODE_KIND::NT_BV_SIGN_EXT:
                condAssert(args.size() == 1, "Invalid number of arguments for sign_extend");
                condAssert(params.size() == 1, "Invalid number of parameters for sign_extend");
                return mkBvSignExt(params[0], args[0]);
            case NODE_KIND::NT_BV_ROTATE_LEFT:
                condAssert(args.size() == 1, "Invalid number of arguments for rotate_left");
                condAssert(params.size() == 1, "Invalid number of parameters for rotate_left");
                return mkBvRotateLeft(params[0], args[0]);
            case NODE_KIND::NT_BV_ROTATE_RIGHT:
                condAssert(args.size() == 1, "Invalid number of arguments for rotate_right");
                condAssert(params.size() == 1, "Invalid number of parameters for rotate_right");
                return mkBvRotateRight(params[0], args[0]);
            case NODE_KIND::NT_FP_ABS:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.abs");
                return mkFpAbs(params[0]);
            case NODE_KIND::NT_FP_NEG:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.neg");
                return mkFpNeg(params[0]);
            case NODE_KIND::NT_FP_ADD:
                return mkFpAdd(params);
            case NODE_KIND::NT_FP_SUB:
                return mkFpSub(params);
            case NODE_KIND::NT_FP_MUL:
                return mkFpMul(params);
            case NODE_KIND::NT_FP_DIV:
                return mkFpDiv(params);
            case NODE_KIND::NT_FP_FMA:
                condAssert(params.size() == 3, "Invalid number of parameters for fp.fma");
                return mkFpFma(params);
            case NODE_KIND::NT_FP_SQRT:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.sqrt");
                return mkFpSqrt(params[0]);
            case NODE_KIND::NT_FP_REM:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.rem");
                return mkFpRem(params[0], params[1]);
            case NODE_KIND::NT_FP_ROUND_TO_INTEGRAL:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.roundToIntegral");
                return mkFpRoundToIntegral(params[0]);
            case NODE_KIND::NT_FP_MIN:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.min");
                return mkFpMin(params);
            case NODE_KIND::NT_FP_MAX:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.max");
                return mkFpMax(params);
            case NODE_KIND::NT_FP_LE:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.le");
                return mkFpLe(params[0], params[1]);
            case NODE_KIND::NT_FP_LT:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.lt");
                return mkFpLt(params[0], params[1]);
            case NODE_KIND::NT_FP_GE:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.ge");
                return mkFpGe(params[0], params[1]);
            case NODE_KIND::NT_FP_GT:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.gt");
                return mkFpGt(params[0], params[1]);
            case NODE_KIND::NT_FP_EQ:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.eq");
                return mkFpEq(params[0], params[1]);
            case NODE_KIND::NT_FP_NE:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.ne");
                return mkFpNe(params[0], params[1]);
            case NODE_KIND::NT_FP_TO_UBV:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.to_ubv");
                return mkFpToUbv(params[0], params[1]);
            case NODE_KIND::NT_FP_TO_SBV:
                condAssert(params.size() == 2, "Invalid number of parameters for fp.to_sbv");
                return mkFpToSbv(params[0], params[1]);
            case NODE_KIND::NT_FP_TO_REAL:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.to_real");
                return mkFpToReal(params[0]);
            case NODE_KIND::NT_FP_TO_FP:
                condAssert(params.size() == 3, "Invalid number of parameters for to_fp");
                return mkToFp(params[0], params[1], params[2]);
            case NODE_KIND::NT_FP_IS_NORMAL:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isNormal");
                return mkFpIsNormal(params[0]);
            case NODE_KIND::NT_FP_IS_SUBNORMAL:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isSubnormal");
                return mkFpIsSubnormal(params[0]);
            case NODE_KIND::NT_FP_IS_ZERO:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isZero");
                return mkFpIsZero(params[0]);
            case NODE_KIND::NT_FP_IS_INF:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isInfinite");
                return mkFpIsInf(params[0]);
            case NODE_KIND::NT_FP_IS_NAN:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isNaN");
                return mkFpIsNan(params[0]);
            case NODE_KIND::NT_FP_IS_NEG:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isNegative");
                return mkFpIsNeg(params[0]);
            case NODE_KIND::NT_FP_IS_POS:
                condAssert(params.size() == 1, "Invalid number of parameters for fp.isPositive");
                return mkFpIsPos(params[0]);
            case NODE_KIND::NT_SELECT:
                condAssert(params.size() == 2, "Invalid number of parameters for select");
                return mkSelect(params[0], params[1]);
            case NODE_KIND::NT_STORE:
                condAssert(params.size() == 3, "Invalid number of parameters for store");
                return mkStore(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_LEN:
                condAssert(params.size() == 1, "Invalid number of parameters for str.len");
                return mkStrLen(params[0]);
            case NODE_KIND::NT_STR_CONCAT:
                return mkStrConcat(params);
            case NODE_KIND::NT_STR_SUBSTR:
                condAssert(params.size() == 3, "Invalid number of parameters for str.substr");
                return mkStrSubstr(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_PREFIXOF:
                condAssert(params.size() == 2, "Invalid number of parameters for str.prefixof");
			    return mkStrPrefixof(params[0], params[1]);
            case NODE_KIND::NT_STR_SUFFIXOF:
                condAssert(params.size() == 2, "Invalid number of parameters for str.suffixof");
                return mkStrSuffixof(params[0], params[1]);
            case NODE_KIND::NT_STR_INDEXOF:
                condAssert(params.size() == 3, "Invalid number of parameters for str.indexof");
                return mkStrIndexof(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_CHARAT:
                condAssert(params.size() == 2, "Invalid number of parameters for str.at");
                return mkStrCharat(params[0], params[1]);
            case NODE_KIND::NT_STR_UPDATE:
                condAssert(params.size() == 3, "Invalid number of parameters for str.update");
                return mkStrUpdate(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_REPLACE:
                condAssert(params.size() == 3, "Invalid number of parameters for str.replace");
                return mkStrReplace(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_REPLACE_ALL:
                condAssert(params.size() == 3, "Invalid number of parameters for str.replace_all");
                return mkStrReplaceAll(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_REPLACE_REG:
                condAssert(params.size() == 3, "Invalid number of parameters for str.replace_re");
                return mkStrReplaceReg(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_REPLACE_REG_ALL:
                condAssert(params.size() == 3, "Invalid number of parameters for str.replace_re_all");
                return mkStrReplaceRegAll(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_INDEXOF_REG:
                condAssert(params.size() == 2, "Invalid number of parameters for str.indexof_re");
                return mkStrIndexofReg(params[0], params[1]);
            case NODE_KIND::NT_STR_TO_LOWER:
                condAssert(params.size() == 1, "Invalid number of parameters for str.to_lower");
                return mkStrToLower(params[0]);
            case NODE_KIND::NT_STR_TO_UPPER:
                condAssert(params.size() == 1, "Invalid number of parameters for str.to_upper");
                return mkStrToUpper(params[0]);
            case NODE_KIND::NT_STR_REV:
                condAssert(params.size() == 1, "Invalid number of parameters for str.rev");
                return mkStrRev(params[0]);
            case NODE_KIND::NT_STR_SPLIT:
                condAssert(params.size() == 2, "Invalid number of parameters for str.split");
                return mkStrSplit(params[0], params[1]);
            case NODE_KIND::NT_STR_SPLIT_AT:
                condAssert(params.size() == 3, "Invalid number of parameters for str.split_at");
                return mkStrSplitAt(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_SPLIT_REST:
                condAssert(params.size() == 3, "Invalid number of parameters for str.split_rest");
                return mkStrSplitRest(params[0], params[1], params[2]);
            case NODE_KIND::NT_STR_NUM_SPLITS:
                condAssert(params.size() == 2, "Invalid number of parameters for str.num_splits");
                return mkStrNumSplits(params[0], params[1]);
            case NODE_KIND::NT_STR_LT:
                condAssert(params.size() == 2, "Invalid number of parameters for str.<");
                return mkStrLt(params[0], params[1]);
            case NODE_KIND::NT_STR_LE:
                condAssert(params.size() == 2, "Invalid number of parameters for str.<=");
                return mkStrLe(params[0], params[1]);
            case NODE_KIND::NT_STR_GT:
                condAssert(params.size() == 2, "Invalid number of parameters for str.>");
                return mkStrGt(params[0], params[1]);
            case NODE_KIND::NT_STR_GE:
                condAssert(params.size() == 2, "Invalid number of parameters for str.>=");
                return mkStrGe(params[0], params[1]);
            case NODE_KIND::NT_STR_IN_REG:
                condAssert(params.size() == 2, "Invalid number of parameters for str.in_re");
                return mkStrInReg(params[0], params[1]);
            case NODE_KIND::NT_STR_CONTAINS:
                condAssert(params.size() == 2, "Invalid number of parameters for str.contains");
                return mkStrContains(params[0], params[1]);
            case NODE_KIND::NT_STR_IS_DIGIT:
                condAssert(params.size() == 1, "Invalid number of parameters for str.is_digit");
                return mkStrIsDigit(params[0]);
            case NODE_KIND::NT_STR_FROM_INT:
                condAssert(params.size() == 1, "Invalid number of parameters for str.from_int");
                return mkStrFromInt(params[0]);
            case NODE_KIND::NT_STR_TO_INT:
                condAssert(params.size() == 1, "Invalid number of parameters for str.to_int");
                return mkStrToInt(params[0]);
            case NODE_KIND::NT_STR_TO_REG:
                condAssert(params.size() == 1, "Invalid number of parameters for str.to_re");
                return mkStrToReg(params[0]);
            case NODE_KIND::NT_STR_TO_CODE:
                condAssert(params.size() == 1, "Invalid number of parameters for str.to_code");
                return mkStrToCode(params[0]);
            case NODE_KIND::NT_STR_FROM_CODE:
                condAssert(params.size() == 1, "Invalid number of parameters for str.from_code");
                return mkStrFromCode(params[0]);
            case NODE_KIND::NT_REG_CONCAT:
                return mkRegConcat(params);
            case NODE_KIND::NT_REG_UNION:
                return mkRegUnion(params);
            case NODE_KIND::NT_REG_INTER:
                return mkRegInter(params);
            case NODE_KIND::NT_REG_DIFF:
                return mkRegDiff(params);
            case NODE_KIND::NT_REG_STAR:
                condAssert(params.size() == 1, "Invalid number of parameters for re.*");
                return mkRegStar(params[0]);
            case NODE_KIND::NT_REG_PLUS:
                condAssert(params.size() == 1, "Invalid number of parameters for re.+");
                return mkRegPlus(params[0]);
            case NODE_KIND::NT_REG_OPT:
                condAssert(params.size() == 1, "Invalid number of parameters for re.?");
                return mkRegOpt(params[0]);
            case NODE_KIND::NT_REG_RANGE:
                condAssert(params.size() == 2, "Invalid number of parameters for re.range");
                return mkRegRange(params[0], params[1]);
            case NODE_KIND::NT_REG_REPEAT:
                condAssert(params.size() == 2, "Invalid number of parameters for re.repeat");
                return mkRegRepeat(params[0], params[1]);
            case NODE_KIND::NT_REG_COMPLEMENT:
                condAssert(params.size() == 1, "Invalid number of parameters for re.comp");
                return mkRegComplement(params[0]);
            case NODE_KIND::NT_REG_LOOP:
                condAssert(params.size() == 1, "Invalid number of parameters for re.loop");
                condAssert(args.size() == 2, "Invalid number of arguments for re.loop");
                return mkRegLoop(params[0], args[0], args[1]);
            case NODE_KIND::NT_FUNC_APPLY:
            case NODE_KIND::NT_FUNC_DEC:
            case NODE_KIND::NT_FUNC_DEF:
                if (fun_key_map.find(s) != fun_key_map.end()) {
                    // function
                    return applyFun(fun_key_map[s], params);
                }
                else {
                    err_unkwn_sym(s, line_number);
                }
                return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
            case NODE_KIND::NT_UNKNOWN:
            case NODE_KIND::NT_ERROR:
            case NODE_KIND::NT_NULL:
            case NODE_KIND::NT_CONST:
            case NODE_KIND::NT_VAR:
            case NODE_KIND::NT_CONST_TRUE:
            case NODE_KIND::NT_CONST_FALSE:
            case NODE_KIND::NT_TEMP_VAR:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:
            case NODE_KIND::NT_LET:
            case NODE_KIND::NT_LET_CHAIN:
            case NODE_KIND::NT_LET_BIND_VAR:
            case NODE_KIND::NT_LET_BIND_VAR_LIST:
            case NODE_KIND::NT_FORALL:
            case NODE_KIND::NT_EXISTS:
            case NODE_KIND::NT_QUANT_VAR:
            case NODE_KIND::NT_FUNC_PARAM:
            case NODE_KIND::NUM_KINDS:
                condAssert(false, "Invalid kind");
            default:
                return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
		}
	}
}