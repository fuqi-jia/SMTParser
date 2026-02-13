/* -*- Header -*-
 * NL2SMT compiler: Natural Language -> SMTParser DAG (assertions + objectives)
 */
#ifndef NL2SMT_NL2SMT_HEADER
#define NL2SMT_NL2SMT_HEADER

#include "parser.h"
#include <memory>
#include <string>

namespace SMTParser {
namespace NL2SMT {

class NL2SMTCompiler {
public:
    explicit NL2SMTCompiler(std::shared_ptr<Parser> parser);

    /** Call LLM with prompt + text, parse model output as SMT-LIB2; on success assertions/objectives written to parser. */
    bool compile(const std::string& text);

    /** Last error/warning message. */
    std::string report() const { return report_; }

private:
    std::shared_ptr<Parser> parser_;
    mutable std::string report_;
};

}  // namespace NL2SMT
}  // namespace SMTParser

#endif
