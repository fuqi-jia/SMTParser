#include <iostream>
#include <string>
#include <vector>
#include "../include/parser.h"

// 测试数组常量和基本操作
void test_array_basics(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "((as const (Array Int Int)) 0)",              // 所有元素为0的Int->Int数组
        "(select ((as const (Array Int Int)) 5) 10)",  // 从常量数组中选择元素
        "(store ((as const (Array Int Int)) 0) 2 42)", // 在索引2处存储42
        "(select (store ((as const (Array Int Int)) 0) 2 42) 2)", // 读取存储的值
        "(select (store ((as const (Array Int Int)) 0) 2 42) 3)"  // 读取未存储的值
    };
    
    std::cout << "=== 测试数组基本操作 ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "表达式: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  结果: " << parser->toString(result) << std::endl;
            
            // 打印表达式的种类
            std::cout << "  种类: " << parser->getKind(result) << std::endl;
            
            // 检查是否为数组类型
            std::cout << "  是否为数组: " << (parser->isArray(result) ? "是" : "否") << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// 测试数组等价性判断
void test_array_equality(SMTParser::ParserPtr& parser) {
    std::vector<std::string> expressions = {
        "(= ((as const (Array Int Int)) 0) ((as const (Array Int Int)) 0))",
        "(= ((as const (Array Int Int)) 0) ((as const (Array Int Int)) 1))",
        "(= (store ((as const (Array Int Int)) 0) 1 5) (store ((as const (Array Int Int)) 0) 1 5))",
        "(= (store ((as const (Array Int Int)) 0) 1 5) (store ((as const (Array Int Int)) 0) 1 6))",
        "(= (store ((as const (Array Int Int)) 0) 1 5) (store ((as const (Array Int Int)) 0) 2 5))"
    };
    
    std::cout << "=== 测试数组等价性 ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "表达式: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  结果: " << parser->toString(result) << std::endl;
            
            // 使用evaluate尝试求值（如果支持）
            try {
                auto evalResult = parser->evaluate(result);
                std::cout << "  求值结果: " << parser->toString(evalResult) << std::endl;
            } catch (const std::exception& e) {
                std::cout << "  求值异常: " << e.what() << std::endl;
            }
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

// 测试复杂数组操作
void test_complex_array_operations(SMTParser::ParserPtr& parser) {
    // 创建变量声明
    parser->declareVar("arr1", "Array Int Int");
    parser->declareVar("arr2", "Array Int Int");
    parser->declareVar("i", "Int");
    parser->declareVar("v", "Int");
    
    std::vector<std::string> expressions = {
        // 使用声明的变量进行操作
        "arr1",
        "(select arr1 i)",
        "(store arr1 i v)",
        "(select (store arr1 i v) i)",
        
        // 嵌套数组操作
        "(store (store arr1 i v) (+ i 1) (+ v 1))",
        "(select (store (store arr1 i v) (+ i 1) (+ v 1)) i)",
        
        // 数组相等断言
        "(= arr1 arr2)",
        "(= arr1 (store arr1 i v))",
        
        // 数组与常量数组比较
        "(= arr1 ((as const (Array Int Int)) 0))"
    };
    
    std::cout << "=== 测试复杂数组操作 ===" << std::endl;
    for (const auto& expr : expressions) {
        std::cout << "表达式: " << expr << std::endl;
        try {
            std::shared_ptr<SMTParser::DAGNode> result = parser->mkExpr(expr);
            std::cout << "  结果: " << parser->toString(result) << std::endl;
            
            // 获取表达式的类型
            try {
                auto type = parser->getType(result);
                std::cout << "  类型: " << type << std::endl;
            } catch (const std::exception& e) {
                std::cout << "  获取类型异常: " << e.what() << std::endl;
            }
        } catch (const std::exception& e) {
            std::cout << "  异常: " << e.what() << std::endl;
        }
        std::cout << std::endl;
    }
}

int main() {
    std::cout << "======= 数组理论测试 =======" << std::endl;
    
    SMTParser::ParserPtr parser = SMTParser::newParser();
    
    test_array_basics(parser);
    test_array_equality(parser);
    test_complex_array_operations(parser);
    
    return 0;
} 