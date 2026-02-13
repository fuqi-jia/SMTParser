/* -*- Source -*-
 * NL2SMT compiler: Natural language -> Prompt + LLM call -> SMT-LIB2 -> Parser (assertions/objectives)
 */
#include "nl2smt/nl2smt.h"
#include "nl2smt/llm_caller.h"
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#if !defined(_WIN32) && !defined(_WIN64)
#include <unistd.h>
#endif

namespace SMTParser {
namespace NL2SMT {

NL2SMTCompiler::NL2SMTCompiler(std::shared_ptr<Parser> parser)
    : parser_(std::move(parser)) {}

bool NL2SMTCompiler::compile(const std::string& text) {
    report_.clear();
    if (!parser_) {
        report_ = "null parser";
        return false;
    }

    std::string smt2 = callLLM(text);
    if (smt2.empty()) {
        report_ = llmCallerLastError();
        return false;
    }

    const char* tmpDir = std::getenv("TMPDIR");
    if (!tmpDir) tmpDir = std::getenv("TEMP");
    if (!tmpDir) tmpDir = "/tmp";
    std::string outPath = std::string(tmpDir) + "/nl2smt_out_";
#ifdef _WIN32
    outPath += "0";
#else
    outPath += std::to_string(static_cast<long>(getpid()));
#endif
    outPath += ".smt2";

    std::ofstream of(outPath);
    if (!of) {
        report_ = "Cannot write temp SMT file: " + outPath;
        return false;
    }
    of << smt2;
    of.close();
    if (!of) {
        report_ = "Failed to write temp file.";
        std::remove(outPath.c_str());
        return false;
    }

    bool ok = parser_->parse(outPath);
    std::remove(outPath.c_str());

    if (!ok) {
        report_ = "Parser failed on LLM output. Check that the model outputs valid SMT-LIB2.";
        return false;
    }
    return true;
}

}  // namespace NL2SMT
}  // namespace SMTParser
