/**
 * Test that the umbrella header <smtparser/parser.h> provides the full API:
 * Parser, Rewriter, Context, Node, etc. One include, no other project headers.
 */
#include "smtparser/parser.h"
#include <cassert>
#include <iostream>

int main() {
    std::cout << "======= Umbrella Header Test =======\n";

    // Parser API (from frontend/parser.h)
    SMTParser::ParserPtr parser = SMTParser::newParser();
    std::shared_ptr<SMTParser::DAGNode> node = parser->mkExpr("(and true false)");
    assert(node && node->isFalse());
    std::cout << "Parser: (and true false) -> " << parser->toString(node) << " OK\n";

    // Rewriter API (from passes/rewriter.h)
    SMTParser::ParserPtr p2 = SMTParser::newParser();
    p2->parseStr("(declare-const x Bool)");
    bool ok = p2->parseStr("(assert (not (not x)))");
    assert(ok);
    std::shared_ptr<SMTParser::DAGNode> n = p2->getAssertions().back();
    SMTParser::Rewriter r(p2->getNodeManager());
    SMTParser::Node simplified = r.rewrite(SMTParser::Node(n));
    assert(simplified);
    std::cout << "Rewriter: (not (not x)) -> " << p2->toString(simplified) << " OK\n";

    // Context / ParserContext (from context + frontend)
    SMTParser::Context& ctx = parser->context();
    (void)ctx.getNodeManager();
    (void)static_cast<SMTParser::ParserContext&>(parser->context()).getAssertions();
    std::cout << "Context/ParserContext OK\n";

    std::cout << "======= Umbrella test passed =======\n";
    return 0;
}
