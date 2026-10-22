#include "somtparser/frontend/parser.h"
#include "test_helpers.h"
#include <set>

using namespace SOMTParser;

int main() {
    Parser parser;
    parser.getOptions()->setExpandFunctions(true);
    VERIFY(parser.parseStr("(set-logic ALL)(push 1)"
        "(define-funs-rec ((even ((x Int)) Bool) (odd ((x Int)) Bool))"
        " ((ite (= x 0) true (odd (- x 1))) (ite (= x 0) false (even (- x 1)))))"
        "(define-fun next ((x Int)) Bool (even (+ x 1)))"
        "(assert (next 3))"));
    auto definitions = parser.getRecursiveDefinitions();
    VERIFY(definitions.size() == 2);
    std::set<Node> symbols{definitions[0].symbol, definitions[1].symbol};
    VERIFY(definitions[0].definition->getFuncParams()[0] != definitions[1].definition->getFuncParams()[0]);
    size_t calls = 0;
    for (const auto& definition : definitions) {
        VERIFY(definition.symbol->getFuncBody()->isNull());
        std::vector<Node> pending{definition.definition->getFuncBody()};
        std::set<Node> visited;
        while (!pending.empty()) {
            auto node = pending.back(); pending.pop_back();
            if (!visited.insert(node).second) continue;
            VERIFY(visited.size() < 40);
            VERIFY(!node->isUFApplication());
            if (node->isFuncRecApplication()) {
                ++calls;
                VERIFY(symbols.count(node->getChild(0)) == 1);
                VERIFY(node->getChild(0)->getFuncBody()->isNull());
            }
            for (auto child : children(node)) pending.push_back(child);
        }
    }
    VERIFY(calls == 2);
    auto oldCall = parser.getAssertions().at(0);
    VERIFY(oldCall->getChild(0) == definitions[0].symbol);
    VERIFY(dumpSMTLIB2(oldCall) == "(even 4)");
    VERIFY(parser.parseStr("(pop 1)"));
    VERIFY(parser.getRecursiveDefinitions().empty());
    VERIFY(parser.getFunctions().empty());
    VERIFY(parser.parseStr("(define-fun-rec even ((x Int)) Bool (even x))(assert (even 4))"));
    auto fresh = parser.getRecursiveDefinitions().at(0);
    VERIFY(fresh.symbol != definitions[0].symbol);
    VERIFY(fresh.definition->getFuncBody()->getChild(0) == fresh.symbol);
    VERIFY(parser.getAssertions().at(0) != oldCall);
    VERIFY(oldCall->getChild(0) == definitions[0].symbol);
    VERIFY(parser.parseStr("(reset)"));
    VERIFY(parser.getRecursiveDefinitions().empty());

    Parser binders;
    binders.getOptions()->setExpandFunctions(true);
    VERIFY(binders.parseStr("(set-logic ALL)"
        "(define-fun f ((x Int)) Bool (and (= x 3) (forall ((x Int)) (= x 7))))"
        "(assert (f 3))"));
    std::vector<Node> pending = binders.getAssertions();
    bool quantified = false;
    while (!pending.empty()) {
        auto node = pending.back(); pending.pop_back();
        VERIFY(!node->isFuncParam());
        if (node->getKind() == NODE_KIND::NT_FORALL) {
            quantified = true;
            auto binder = node->getQuantVars().at(0);
            auto body = node->getQuantBody();
            VERIFY(body->getChild(0) == binder || body->getChild(1) == binder);
        }
        for (auto child : children(node)) pending.push_back(child);
    }
    VERIFY(quantified);

    for (const auto& source : std::vector<std::string>{
        "(define-fun-rec f ((x Int)) Bool true)(define-fun-rec f ((x Int)) Bool false)",
        "(define-funs-rec ((f ((x Int)) Bool) (f ((y Int)) Bool)) (true false))",
        "(define-funs-rec ((f ((x Int) (x Int)) Bool)) (true))",
        "(define-fun-rec f ((x Int)) Bool x)",
        "(define-fun-rec f ((x Int)) Bool (f true))",
        "(define-fun-rec f ((x Int)) Bool (f x x))"}) {
        Parser invalid;
        VERIFY(!invalid.parseStr("(set-logic ALL)" + source));
    }
    std::cout << "native binding and recursive symbol regressions passed\n";
}
