#include <iostream>
#include <memory>
#include "../../include/parser.h"

using namespace SMTParser;

int main() {
    try {
        SMTParser::ParserPtr parser = SMTParser::newParser();
        
        std::cout << "=== 调试to_fp表达式args数组顺序 ===" << std::endl;
        
        std::string to_fp_expr = "((_ to_fp 8 24) RNE 3.14159)";
        std::cout << "表达式: " << to_fp_expr << std::endl;
        
        try {
            std::shared_ptr<DAGNode> result = parser->mkExpr(to_fp_expr);
            if (result->isErr()) {
                std::cout << "解析失败: " << parser->toString(result) << std::endl;
            } else {
                std::cout << "解析成功: " << parser->toString(result) << std::endl;
            }
        } catch (const std::exception& e) {
            std::cout << "异常: " << e.what() << std::endl;
        }
        
        std::cout << "\n=== 测试单独解析各个部分 ===" << std::endl;
        
        std::cout << "解析 RNE:" << std::endl;
        try {
            std::shared_ptr<DAGNode> rne = parser->mkExpr("RNE");
            std::cout << "  结果: " << parser->toString(rne) << std::endl;
            std::cout << "  类型: " << rne->getSort()->toString() << std::endl;
            std::cout << "  是舍入模式: " << (rne->getSort()->isRoundingMode() ? "true" : "false") << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        
        std::cout << "解析 3.14159:" << std::endl;
        try {
            std::shared_ptr<DAGNode> real = parser->mkExpr("3.14159");
            std::cout << "  结果: " << parser->toString(real) << std::endl;
            std::cout << "  类型: " << real->getSort()->toString() << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        
        std::cout << "解析 8:" << std::endl;
        try {
            std::shared_ptr<DAGNode> eight = parser->mkExpr("8");
            std::cout << "  结果: " << parser->toString(eight) << std::endl;
            std::cout << "  类型: " << eight->getSort()->toString() << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        
        std::cout << "解析 24:" << std::endl;
        try {
            std::shared_ptr<DAGNode> twenty_four = parser->mkExpr("24");
            std::cout << "  结果: " << parser->toString(twenty_four) << std::endl;
            std::cout << "  类型: " << twenty_four->getSort()->toString() << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        
    } catch (const std::exception& e) {
        std::cout << "主异常: " << e.what() << std::endl;
    }
    
    return 0;
} 