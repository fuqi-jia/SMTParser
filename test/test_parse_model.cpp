#include "parser.h"
#include <iostream>
#include <string>

int main() {
    // 创建解析器
    auto parser = SMTParser::newParser();
    
    // 测试用的SMT-LIB模型字符串
    std::string model_str = R"(
(model 
        (define-fun b.counter.2__AT2 () Bool
                false
        )
        (define-fun b.counter.3__AT2 () Bool
                false
        )
        (define-fun b.EVENT.0__AT1 () Bool
                true
        )
        (define-fun b.delta__AT1 () Real
                0
        )
        (define-fun b.y__AT3 () Real
                (/ 51 10)
        )
        (define-fun b.time__AT1 () Real
                (/ 25 49)
        )
        (define-fun b.speed_y__AT1 () Real
                (- 5)
        )
)";
    
    try {
        // 解析模型
        auto model = parser->parseModel(model_str);
        
        if (model) {
            std::cout << "模型解析成功！" << std::endl;
            std::cout << "模型大小: " << model->size() << std::endl;
            
            // 打印模型内容
            auto pairs = model->getPairs();
            for (const auto& pair : pairs) {
                std::cout << "变量: " << pair.first << " = " << parser->toString(pair.second) << std::endl;
            }
        } else {
            std::cout << "模型解析失败！" << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "解析过程中出现异常: " << e.what() << std::endl;
    }
    
    return 0;
}
