#include "parser.h"
#include <iostream>
#include <string>

int main() {
    // 创建解析器
    auto parser = SMTParser::newParser();
    
    // 测试用的SMT-LIB模型字符串
    std::string model_str1 = R"(
(model
  (define-fun v17 () Real
    0.0)
  (define-fun v15 () Real
    (- 1.0))
  (define-fun v7 () Real
    1.0)
  (define-fun v12 () Real
    (- 1.0))
  (define-fun v1 () Real
    1.0)
  (define-fun v13 () Real
    (- 1.0))
  (define-fun v6 () Real
    (- (/ 1.0 4.0)))
  (define-fun v2 () Real
    1.0)
  (define-fun v16 () Real
    1.0)
  (define-fun v18 () Real
    (- 1.0))
  (define-fun v10 () Real
    (/ 1.0 2.0))
  (define-fun v3 () Real
    0.0)
  (define-fun v14 () Real
    (- 8.0))
  (define-fun v9 () Real
    1.0)
  (define-fun v11 () Real
    1.0)
  (define-fun v4 () Real
    (- (/ 1.0 4.0)))
  (define-fun v5 () Real
    0.0)
  (define-fun v8 () Real
    0.0)
  (define-fun hypothesis () Bool
    (let ((a!1 (+ (* v10 (* v2 v2) v5) (* (- 1.0) v1 v10 v2 v7) (* (* v2 v2) v7 v9))))
  (and (> v4 (- 1.0))
       (> v7 0.0)
       (> a!1 0.0)
       (< v4 0.0)
       (< v6 0.0)
       (< a!1 (* v2 v2)))))
  (define-fun assumptions () Bool
    (let ((a!1 (= (+ (* v14 v18 (* v2 v2 v2) v4) (* v14 v17 (* v2 v2 v2) v7))
              (+ (* v16 v17 (* v2 v2 v2) v4)
                 (* (- 1.0) v1 v12 (* v16 v16) v2 v5)
                 (* (* v1 v1) v12 (* v16 v16) v7)
                 (* v15 v16 (* v2 v2 v2) v7))))
      (a!2 (= (+ v2
                 (* v2 v4)
                 (* (- 1.0) v2 v5)
                 (* (- 1.0) v10 v2 v5)
                 (* v2 v6)
                 (* v1 v10 v7)
                 (* (- 1.0) v2 v7 v9))
              0.0))
      (a!3 (= (+ (* v18 v4)
                 (* 2.0 v18 v3 v4)
                 (* v18 (* v3 v3) v4)
                 (* v17 v7)
                 (* 2.0 v17 v3 v7)
                 (* v17 (* v3 v3) v7)
                 (* v11 v8))
              (+ (* v13 v6) (* v13 v3 v6)))))
  (and (> (* v14 v18) (* v16 v17))
       (> (* v14 v17) (* v15 v16))
       (> (* v2 v9) 0.0)
       (> (* v2 v2 v9) (* v1 v10 v2))
       (< (* (* v1 v1) v12 v2) 0.0)
       (> v10 0.0)
       (< (* v12 v2) 0.0)
       (> v1 0.0)
       (> v2 0.0)
       (> v11 0.0)
       (< v13 0.0)
       (> v3 (- 1.0))
       (> v16 0.0)
       (< v14 0.0)
       (< v18 0.0)
       (< v15 0.0)
       (> (* v15 v18) (* v17 v17))
       a!1
       a!2
       a!3
       (= v8 0.0)
       (= v5 0.0))))
  (define-fun /0 ((x!0 Real) (x!1 Real)) Real
    (ite (and (= x!0 (- (/ 1.0 4.0))) (= x!1 1.0)) (- (/ 1.0 4.0))
      0.0))
)
)";

    std::string model_str2 = R"(
    (
  (define-fun | | () (_ BitVec 4)
    #xc)
  (define-fun v1 () (_ BitVec 4)
    #x0)
  (define-fun ?v0 () (_ BitVec 4)
    #x1)
  (define-fun notes () (_ BitVec 4)
    #x7)
  (define-fun V0 () (_ BitVec 4)
    #x5)
  (define-fun ~!@$%^&*_-+=><.?/ () (_ BitVec 4)
    #xa)
  (define-fun |~!@$%^&*_-+=<>.?/()| () (_ BitVec 4)
    #xe)
  (define-fun v0 () (_ BitVec 4)
    #xf)
  (define-fun  () (_ BitVec 4)
    #x3)
  (define-fun ~!@$%^&*_-+=<>.?/ () (_ BitVec 4)
    #xf)
)
    )";

    
    try {
        // 解析模型
        auto model = parser->parseModel(model_str1);
        
        if (model) {
            std::cout << "模型1解析成功！" << std::endl;
            std::cout << "模型1大小: " << model->size() << std::endl;
            
            // 打印模型内容
            auto pairs = model->getPairs();
            for (const auto& pair : pairs) {
                std::cout << "变量: " << pair.first << " = " << parser->toString(pair.second) << std::endl;
            }
        } else {
            std::cout << "模型2解析失败！" << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "解析过程中出现异常: " << e.what() << std::endl;
    }

    try {
        // 解析模型
        auto model = parser->parseModel(model_str2);
        
        if (model) {
            std::cout << "模型2解析成功！" << std::endl;
            std::cout << "模型2大小: " << model->size() << std::endl;
            
            // 打印模型内容
            auto pairs = model->getPairs();
            for (const auto& pair : pairs) {
                std::cout << "变量: " << pair.first << " = " << parser->toString(pair.second) << std::endl;
            }
        }
        else {
            std::cout << "模型2解析失败！" << std::endl;
        }
    } catch (const std::exception& e) {
        std::cout << "解析过程中出现异常: " << e.what() << std::endl;
    }
    
    return 0;
}
