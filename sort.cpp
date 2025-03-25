/* -*- Source -*-
 *
 * The Sort Class
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

#include "sort.h"

namespace SMTLIBParser{

    std::shared_ptr<Sort> mkBVSort(size_t width){
        return std::make_shared<Sort>(SORT_KIND::SK_BV, "BV", 0, std::vector<std::shared_ptr<Sort>>{std::make_shared<Sort>(SORT_KIND::SK_NULL, "Width", width)});

    }
    std::shared_ptr<Sort> mkFPSort(size_t exp, size_t sig){
        return std::make_shared<Sort>(SORT_KIND::SK_FP, "FP", 0, std::vector<std::shared_ptr<Sort>>{std::make_shared<Sort>(SORT_KIND::SK_NULL, "Exp", exp), std::make_shared<Sort>(SORT_KIND::SK_NULL, "Sig", sig)});
    }
    std::shared_ptr<Sort> mkArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem){
        return std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0, std::vector<std::shared_ptr<Sort>>{index, elem});
    }
}