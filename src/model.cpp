/* -*- Source -*-
 *
 * An SMT/OMT Parser (Model part)
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

#include "include/model.h"

namespace SMTLIBParser{
    Model::Model(){

    }

    Model::~Model(){

    }

    void Model::add(const std::shared_ptr<DAGNode> &node, const std::shared_ptr<DAGNode> &value){
        if(model_name_index.find(node->getName()) != model_name_index.end()){
            model_values[model_name_index[node->getName()]] = value;
        }
        else{
            model_name_index[node->getName()] = model_vars.size();
            model_vars.push_back(node);
            model_values.push_back(value);
        }
    }

    void Model::add(const std::string &name, const std::shared_ptr<DAGNode> &value){
        assert(model_name_index.find(name) != model_name_index.end());
        model_values[model_name_index[name]] = value;
    }

    std::shared_ptr<DAGNode> Model::get(const std::shared_ptr<DAGNode> &node){
        if(model_name_index.find(node->getName()) != model_name_index.end()){
            return model_values[model_name_index[node->getName()]];
        }
        return nullptr;
    }

    std::shared_ptr<DAGNode> Model::get(const std::string &name){
        if(model_name_index.find(name) != model_name_index.end()){
            return model_values[model_name_index[name]];
        }
        return nullptr;
    }

    void Model::addVar(const std::shared_ptr<DAGNode> &node){
        if(model_name_index.find(node->getName()) != model_name_index.end()){
            return;
        }
        model_name_index[node->getName()] = model_vars.size();
        model_vars.push_back(node);
        model_values.push_back(NULL_NODE);
    }

    bool Model::isFull() const{
        for(size_t i = 0; i < model_vars.size(); i++){
            if(model_values[i]->isNull()){
                return false;
            }
        }
        return true;
    }

    std::string Model::toString(){
        std::stringstream ss;
        for(size_t i = 0; i < model_vars.size(); i++){
            ss << "(define-fun " << model_vars[i]->getName() << " () " << model_vars[i]->getSort()->toString() << " " << dumpSMTLIB2(model_values[i]) << ")" << std::endl;
        }
        return ss.str();
    }

    ModelPtr newModel(){
        return std::make_shared<Model>();
    }
}
