#include <iostream>
#include <string>
#include <vector>
#include <gmpxx.h>
#include "somtparser/frontend/parser.h"
#include "somtparser/model/model.h"
#include "somtparser/core/util.h"
#include "test_helpers.h"

using namespace SOMTParser;

static void expectInteger(const Node& node, const mpz_class& expected) {
    VERIFY(node && node->isConst() && node->getSort()->isInt());
    VERIFY(node->getValue());
    VERIFY(node->getValue()->getNumberValue().toString() == expected.get_str());
}

static mpz_class euclideanChain(mpz_class value, const std::vector<mpz_class>& divisors) {
    for(const auto& divisor : divisors) {
        VERIFY(divisor != 0);
        const mpz_class modulus = abs(divisor);
        mpz_fdiv_q(value.get_mpz_t(), value.get_mpz_t(), modulus.get_mpz_t());
        if(divisor < 0) value = -value;
    }
    return value;
}

static std::string numeral(const mpz_class& value) {
    return value < 0 ? "(- " + mpz_class(-value).get_str() + ")" : value.get_str();
}

static void parsedAndConstructedModels() {
    const std::vector<std::vector<mpz_class>> chains{
        {2, 2}, {3, -2}, {-3, 2}, {-3, -2}, {-3, 2, -2},
        {1000003, -1000033, 1000037}};
    const mpz_class huge("123456789012345678901234567890123456789012345678901234567890123456789");
    const std::vector<mpz_class> values{-huge, -13, -1, 0, 1, 13, huge};
    for(const auto& divisors : chains) {
        ParserPtr parser = newParser();
        auto x = parser->declareVar("x", "Int");
        std::vector<Node> operands{x};
        std::string text = "(div x";
        for(const auto& divisor : divisors) {
            operands.push_back(parser->mkConstInt(divisor.get_str()));
            text += " " + numeral(divisor);
        }
        text += ")";
        auto parsed = parser->mkExpr(text);
        auto built = parser->mkDivInt(operands);
        VERIFY(parsed && parsed->getKind() == NODE_KIND::NT_DIV_INT);
        VERIFY(parsed->getChildrenSize() == operands.size());
        VERIFY(parsed == built); // same typed DAG through both public entry points
        const auto printed = dumpSMTLIB2(parsed);
        ParserPtr again = newParser();
        again->declareVar("x", "Int");
        auto roundTrip = again->mkExpr(printed);
        VERIFY(roundTrip && roundTrip->getChildrenSize() == operands.size());
        VERIFY(dumpSMTLIB2(roundTrip) == printed);
        for(const auto& value : values) {
            auto model = newModel();
            model->add(x, parser->mkConstInt(value.get_str()));
            const auto expected = euclideanChain(value, divisors);
            expectInteger(parser->evaluate(parsed, model), expected);
            expectInteger(parser->evaluate(built, model), expected);
            std::string constantText = "(div " + numeral(value);
            for(const auto& divisor : divisors) constantText += " " + numeral(divisor);
            constantText += ")";
            expectInteger(parser->mkExpr(constantText), expected);
        }
    }
}

static void binaryAndPartialModels() {
    ParserPtr parser = newParser();
    auto x = parser->declareVar("x", "Int");
    auto y = parser->declareVar("y", "Int");
    for(const auto& expression : std::vector<std::string>{"(div x y)", "(div x y 2)", "(div x 2 y)"}) {
        auto term = parser->mkExpr(expression);
        auto first = newModel();
        first->add(x, parser->mkConstInt(13));
        auto residual = parser->evaluate(term, first);
        VERIFY(residual && !residual->isConst() && !residual->isNull() && !residual->isUnknown());
        auto second = newModel();
        second->add(y, parser->mkConstInt(-3));
        const mpz_class expected = expression == "(div x y)" ? -4 : -2;
        expectInteger(parser->evaluate(residual, second), expected);
        auto full = newModel();
        full->add(x, parser->mkConstInt(13));
        full->add(y, parser->mkConstInt(-3));
        expectInteger(parser->evaluate(term, full), expected);
    }
    // Multiplying signed divisors is unsound:
    // div(div(-7,-3),-2)=-1, whereas div(-7,6)=-2.
    auto negative = newModel();
    negative->add(x, parser->mkConstInt(-7));
    expectInteger(parser->evaluate(parser->mkExpr("(div x (- 3) (- 2))"), negative), -1);
}

static void zeroDivisionAndPreservation() {
    ParserPtr parser = newParser();
    auto x = parser->declareVar("x", "Int");
    auto term = parser->mkExpr("(div x 0 2)");
    auto model = newModel();
    model->add(x, parser->mkConstInt(13));
    auto residual = parser->evaluate(term, model);
    VERIFY(residual && !residual->isConst() && !residual->isNull());
    VERIFY(dumpSMTLIB2(residual).find(" 0)") != std::string::npos);
    auto constant = parser->mkExpr("(div 13 0 2)");
    VERIFY(constant && !constant->isConst());
    parser->getOptions()->preserveOperator(NODE_KIND::NT_DIV_INT);
    auto kept = parser->mkExpr("(div 13 2 2)");
    VERIFY(kept && kept->getKind() == NODE_KIND::NT_DIV_INT && kept->getChildrenSize() == 3);
}

static void scriptParsingAndRejection() {
    ParserPtr parser = newParser();
    VERIFY(parser->parseStr("(set-logic LIA)(declare-const x Int)"
                           "(assert (= (div x 2 2) 3))"));
    bool found = false;
    std::vector<Node> pending = parser->getAssertions();
    while(!pending.empty()) {
        auto node = pending.back(); pending.pop_back();
        if(node->getKind() == NODE_KIND::NT_DIV_INT) {
            found = true;
            VERIFY(node->getChildrenSize() == 3);
        }
        for(auto child : node->getChildren()) pending.push_back(child);
    }
    VERIFY(found);
    for(const auto& expression : std::vector<std::string>{"(div)", "(div x)",
            "(div x true 2)", "(div true x 2)", "(div x 2 true)", "(div x 2 r)"}) {
        ParserPtr bad = newParser();
        VERIFY(!bad->parseStr("(set-logic ALL)(declare-const x Int)(declare-const r Real)"
                              "(assert (= " + expression + " 0))"));
    }
}

int main() {
    parsedAndConstructedModels();
    binaryAndPartialModels();
    zeroDivisionAndPreservation();
    scriptParsingAndRejection();
    std::cout << "n-ary integer division parsing, evaluation and round trips passed\n";
}
