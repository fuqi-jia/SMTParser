#include "somtparser/frontend/parser.h"
#include "test_helpers.h"
#include <set>

using namespace SOMTParser;

int main() {
    for (bool preserve : {false, true}) {
        Parser p;
        p.getOptions()->parsing_preserve_let = preserve;
        VERIFY(p.parseStr("(set-logic ALL)(assert (let ((x 2)) (let ((x 1) (y x)) (= y 2))))"));
        auto n = p.getAssertions().at(0);
        std::vector<Node> pending{n};
        bool hasFalse = false;
        while (!pending.empty()) {
            auto current = pending.back(); pending.pop_back();
            hasFalse |= current->isFalse();
            for (auto c : children(current)) pending.push_back(c);
        }
        VERIFY(!hasFalse);
        if (!preserve) VERIFY(n->isTrue());
    }
    Parser binders;
    VERIFY(binders.parseStr("(set-logic ALL)(assert (forall ((x Int))"
        " (and (= x 0) (exists ((x Int)) (= x 1)) (= x 2))))"));
    auto outer = binders.getAssertions().at(0)->getQuantVars().at(0);
    std::vector<Node> pending = binders.getAssertions();
    size_t innerCount = 0;
    while (!pending.empty()) {
        auto n = pending.back(); pending.pop_back();
        if (n->getKind() == NODE_KIND::NT_EXISTS) {
            ++innerCount;
            auto inner = n->getQuantVars().at(0);
            VERIFY(inner != outer);
            auto body = n->getQuantBody();
            VERIFY(body->getChild(0) == inner || body->getChild(1) == inner);
        }
        for (auto c : children(n)) pending.push_back(c);
    }
    VERIFY(innerCount == 1);

    Parser heap;
    VERIFY(heap.parseStr("(set-logic ALL)(declare-heap (Int Int))(declare-const x Int)"
        "(assert (wand (pto x 1) (sep sep.emp (pto x 1))))"));
    VERIFY(heap.getHeapLocationSort()->isInt());
    VERIFY(heap.getHeapDataSort()->isInt());
    auto saved = heap.getAssertions().at(0);
    const auto savedText = dumpSMTLIB2(saved);
    VERIFY(saved->getKind() == NODE_KIND::NT_SEP_WAND);
    VERIFY(dumpSMTLIB2(heap.mkExpr("(as sep.nil Int)")) == "(as sep.nil Int)");
    VERIFY(heap.parseStr("(reset-assertions)(declare-const x Int)(assert sep.emp)"));
    VERIFY(heap.getHeapLocationSort()->isInt());
    VERIFY(heap.parseStr("(reset)(set-logic ALL)(declare-heap (Bool Int))"));
    VERIFY(heap.getHeapLocationSort()->isBool());
    VERIFY(dumpSMTLIB2(saved) == savedText);
    heap.getNodeManager()->clear();
    VERIFY(dumpSMTLIB2(saved) == savedText);

    for (const auto& source : std::vector<std::string>{
        "(assert sep.emp)",
        "(declare-heap (Int Int))(declare-heap (Int Int))",
        "(push 1)(declare-heap (Int Int))",
        "(declare-heap (Int Int))(assert (pto true 1))",
        "(declare-heap (Int Int))(assert (pto (as sep.nil Bool) 1))",
        "(pop 1)"}) {
        Parser invalid;
        VERIFY(!invalid.parseStr("(set-logic ALL)" + source));
    }
    std::cout << "native heap and binder regressions passed\n";
}
