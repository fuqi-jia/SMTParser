/* -*- Source -*-
 * NL2SMT compiler: NL -> Tree-Plan (JSON) -> Emit (SMT-LIB2) -> Parse [-> Repair loop]
 */
#include "nl2smt/nl2smt.h"
#include "nl2smt/llm_caller.h"
#include <cstdlib>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#if defined(_WIN32) || defined(_WIN64)
#include <direct.h>
#else
#include <sys/stat.h>
#include <unistd.h>
#endif

namespace SMTParser {
namespace NL2SMT {

namespace {

bool hasRequiredKeys(const std::string& json) {
    return json.find("\"symbols\"") != std::string::npos
        && json.find("\"constraints\"") != std::string::npos
        && json.find("\"objective\"") != std::string::npos;
}

/** Best-effort: collect "name": "x" from symbols array. */
void collectSymbolNames(const std::string& json, std::vector<std::string>& out) {
    out.clear();
    size_t pos = 0;
    for (;;) {
        pos = json.find("\"name\"", pos);
        if (pos == std::string::npos) break;
        pos = json.find(':', pos);
        if (pos == std::string::npos) break;
        pos = json.find('"', pos + 1);
        if (pos == std::string::npos) break;
        size_t start = pos + 1;
        size_t end = json.find('"', start);
        if (end == std::string::npos) break;
        out.push_back(json.substr(start, end - start));
        pos = end + 1;
    }
}

/** Best-effort: collect "var": "x" from constraints/objective. */
void collectVarRefs(const std::string& json, std::vector<std::string>& out) {
    out.clear();
    size_t pos = 0;
    for (;;) {
        pos = json.find("\"var\"", pos);
        if (pos == std::string::npos) break;
        pos = json.find(':', pos);
        if (pos == std::string::npos) break;
        pos = json.find('"', pos + 1);
        if (pos == std::string::npos) break;
        size_t start = pos + 1;
        size_t end = json.find('"', start);
        if (end == std::string::npos) break;
        out.push_back(json.substr(start, end - start));
        pos = end + 1;
    }
}

/** After "\"args\": [", count top-level elements (arity) by counting commas at depth 1. */
static int countArgsArity(const std::string& json, size_t argsStart) {
    size_t i = json.find('[', argsStart);
    if (i == std::string::npos) return 0;
    int depth = 1;
    int count = 1;
    for (++i; i < json.size() && depth > 0; ++i) {
        char c = json[i];
        if (c == '[') ++depth;
        else if (c == ']') --depth;
        else if (c == ',' && depth == 1) ++count;
    }
    return depth == 0 ? count : 0;
}

/** Extract op name after "\"op\":" up to next quote. */
static std::string extractOp(const std::string& json, size_t opKeyStart) {
    size_t colon = json.find(':', opKeyStart);
    if (colon == std::string::npos) return "";
    size_t q = json.find('"', colon);
    if (q == std::string::npos) return "";
    size_t start = q + 1;
    size_t end = json.find('"', start);
    if (end == std::string::npos) return "";
    return json.substr(start, end - start);
}

}  // namespace

NL2SMTCompiler::NL2SMTCompiler(std::shared_ptr<Parser> parser)
    : parser_(std::move(parser)) {}

bool NL2SMTCompiler::validatePlanArity(const std::string& planJson) {
    size_t pos = 0;
    while ((pos = planJson.find("\"op\"", pos)) != std::string::npos) {
        std::string op = extractOp(planJson, pos);
        size_t argsKey = planJson.find("\"args\"", pos);
        if (argsKey == std::string::npos) { pos++; continue; }
        int arity = countArgsArity(planJson, argsKey);
        if (op == "not" && arity != 1) return false;
        if ((op == "and" || op == "or") && arity < 1) return false;
        if (op == "implies" && arity != 2) return false;
        if (op == "ite" && arity != 3) return false;
        if ((op == "=" || op == "<" || op == "<=" || op == ">" || op == ">=") && arity != 2) return false;
        if ((op == "+" || op == "-" || op == "*" || op == "div" || op == "mod") && arity < 2) return false;
        pos = argsKey + 1;
    }
    return true;
}

bool NL2SMTCompiler::validatePlan(const std::string& planJson, bool doTypecheck) {
    if (planJson.empty()) return false;
    if (planJson.find('{') == std::string::npos || planJson.find('}') == std::string::npos)
        return false;
    if (!hasRequiredKeys(planJson)) return false;
    std::vector<std::string> symbols, vars;
    collectSymbolNames(planJson, symbols);
    collectVarRefs(planJson, vars);
    for (const auto& v : vars) {
        bool found = false;
        for (const auto& s : symbols) {
            if (s == v) { found = true; break; }
        }
        if (!found) return false;
    }
    if (doTypecheck && !validatePlanArity(planJson)) return false;
    return true;
}

bool NL2SMTCompiler::compile(const std::string& text) {
    report_.clear();
    last_repair_count_ = -1;
    if (!parser_) {
        report_ = "null parser";
        return false;
    }

    std::string planJson = callLLM_Plan(text);
    if (planJson.empty()) {
        std::string err = llmCallerLastError();
        const char* scriptEnv = std::getenv("NL2SMT_LLM_SCRIPT");
        bool haveScript = (scriptEnv && scriptEnv[0] != '\0');
        /* Fallback to CMD when: no SCRIPT configured (legacy), or SCRIPT failed and --nl-fallback-cmd set. */
        if (!haveScript || options_.fallback_cmd) {
            std::string smt2 = callLLM(text);
            if (smt2.empty()) {
                report_ = llmCallerLastError();
                return false;
            }
            const char* tmpDir = std::getenv("TMPDIR");
            if (!tmpDir) tmpDir = std::getenv("TEMP");
            if (!tmpDir) tmpDir = "/tmp";
            std::string outPath = std::string(tmpDir) + "/nl2smt_out_";
#if defined(_WIN32) || defined(_WIN64)
            outPath += "0";
#else
            outPath += std::to_string(static_cast<long>(getpid()));
#endif
            outPath += ".smt2";
            std::ofstream of(outPath);
            if (!of) { report_ = "Cannot write temp SMT file."; return false; }
            of << smt2;
            of.close();
            bool ok = parser_->parse(outPath);
            if (!options_.keep_tmp) std::remove(outPath.c_str());
            if (!ok) report_ = "Parser failed on LLM output.";
            last_repair_count_ = 0;
            return ok;
        }
        report_ = err;
        return false;
    }

    if (options_.plan_only) {
        report_ = planJson;
        return true;
    }

    bool doTypecheck = !options_.no_typecheck;
    if (!validatePlan(planJson, doTypecheck)) {
        report_ = doTypecheck
            ? "Plan validation failed: missing required keys, variable not in symbols, or arity/sort check."
            : "Plan validation failed: missing required keys or variable not in symbols.";
        return false;
    }

    const char* tmpDir = std::getenv("TMPDIR");
    if (!tmpDir) tmpDir = std::getenv("TEMP");
    if (!tmpDir) tmpDir = "/tmp";
    std::string artifactDir = options_.artifact_dir;
    if (!artifactDir.empty() && artifactDir.back() != '/' && artifactDir.back() != '\\')
        artifactDir += '/';
    if (!artifactDir.empty()) {
        std::string dirForMkdir = artifactDir;
        if (!dirForMkdir.empty() && (dirForMkdir.back() == '/' || dirForMkdir.back() == '\\'))
            dirForMkdir.pop_back();
        if (!dirForMkdir.empty()) {
#if defined(_WIN32) || defined(_WIN64)
            (void)_mkdir(dirForMkdir.c_str());  /* ignore error; EEXIST ok */
#else
            (void)mkdir(dirForMkdir.c_str(), 0755);  /* ignore error; EEXIST ok */
#endif
        }
        std::ofstream(artifactDir + "nl.txt") << text;
        std::ofstream(artifactDir + "plan.json") << planJson;
    }

    std::string smt2 = callLLM_Emit(planJson);
    if (smt2.empty()) {
        report_ = llmCallerLastError();
        return false;
    }
    if (!artifactDir.empty()) {
        std::ofstream(artifactDir + "emit.smt2") << smt2;
    }

    std::string outPath = std::string(tmpDir) + "/nl2smt_out_";
#if defined(_WIN32) || defined(_WIN64)
    outPath += "0";
#else
    outPath += std::to_string(static_cast<long>(getpid()));
#endif
    outPath += ".smt2";

    for (int repairRound = 0; repairRound <= options_.max_repair; ++repairRound) {
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

        std::ostringstream parserErrCapture;
        std::streambuf* oldCout = std::cout.rdbuf(parserErrCapture.rdbuf());
        bool ok = parser_->parse(outPath);
        std::cout.rdbuf(oldCout);
        std::string parserError = parserErrCapture.str();
        if (!artifactDir.empty()) {
            std::ofstream(artifactDir + "parse_error.txt") << parserError;
            std::ofstream(artifactDir + "repair_" + std::to_string(repairRound) + ".smt2") << smt2;
        }
        if (!options_.keep_tmp) std::remove(outPath.c_str());

        if (ok) {
            last_repair_count_ = repairRound;
            if (options_.roundtrip_check) {
                std::string dumped = parser_->dumpSMT2();
                std::string rtPath = std::string(tmpDir) + "/nl2smt_rt_";
#if defined(_WIN32) || defined(_WIN64)
                rtPath += "0";
#else
                rtPath += std::to_string(static_cast<long>(getpid()));
#endif
                rtPath += ".smt2";
                std::ofstream rtFile(rtPath);
                if (rtFile) {
                    rtFile << dumped;
                    rtFile.close();
                    std::ostringstream rtErr;
                    std::streambuf* oldCout2 = std::cout.rdbuf(rtErr.rdbuf());
                    bool rtOk = parser_->parse(rtPath);
                    std::cout.rdbuf(oldCout2);
                    std::remove(rtPath.c_str());
                    if (!rtOk) {
                        report_ = "Round-trip check failed: parse(dump(parse(emit(plan)))) did not succeed.";
                        return false;
                    }
                }
            }
            return true;
        }

        if (options_.no_repair || repairRound == options_.max_repair) {
            report_ = parserError.empty() ? "Parser failed on LLM output." : parserError;
            return false;
        }

        smt2 = callLLM_Repair(parserError, planJson, smt2);
        if (smt2.empty()) {
            report_ = llmCallerLastError();
            return false;
        }
    }

    report_ = "Parser failed after max repair attempts.";
    return false;
}

}  // namespace NL2SMT
}  // namespace SMTParser
