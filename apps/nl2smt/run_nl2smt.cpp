/* -*- Source -*-
 * NL2SMT app: build options from config/CLI and call Parser::parseNL (library).
 */
#if defined(BUILD_NL2SMT) && defined(SMTLIBPARSER_ENABLE_NL2SMT)

#include "nl2smt/run_nl2smt.h"
#include <cstdlib>
#include <cstring>
#include <string>

#if defined(_WIN32) || defined(_WIN64)
#define getenv_safe(k) (getenv(k) ? getenv(k) : "")
#else
#define getenv_safe(k) (getenv(k) ? getenv(k) : "")
#endif

namespace SMTParser {
namespace NL2SMT {

namespace {

static std::string getConfigOrEnv(const std::map<std::string, std::string>& m,
                                  const std::string& key,
                                  const char* envName,
                                  const std::string& defaultValue) {
    auto it = m.find(key);
    if (it != m.end() && !it->second.empty()) return it->second;
    if (envName) {
        const char* v = getenv_safe(envName);
        if (v && v[0] != '\0') return std::string(v);
    }
    return defaultValue;
}

static int getConfigInt(const std::map<std::string, std::string>& m,
                       const std::string& key, int defaultValue) {
    auto it = m.find(key);
    if (it == m.end() || it->second.empty()) return defaultValue;
    int v = defaultValue;
    try { v = std::stoi(it->second); } catch (...) {}
    return v;
}

static double getConfigDouble(const std::map<std::string, std::string>& m,
                              const std::string& key, double defaultValue) {
    auto it = m.find(key);
    if (it == m.end() || it->second.empty()) return defaultValue;
    double v = defaultValue;
    try { v = std::stod(it->second); } catch (...) {}
    return v;
}

static smtlib::NLCompilationStrategy strategyFromString(const std::string& s) {
    if (s == "Structured")   return smtlib::NLCompilationStrategy::Structured;
    if (s == "DirectTextual") return smtlib::NLCompilationStrategy::DirectTextual;
    return smtlib::NLCompilationStrategy::Structured;
}

}  // namespace

smtlib::NL2SMTOptions buildOptions(
    const std::map<std::string, std::string>& config_nl2smt,
    const NLCliOverrides& cli) {
    smtlib::NL2SMTOptions opt;
    opt.endpoint   = getConfigOrEnv(config_nl2smt, "endpoint",   "NL2SMT_ENDPOINT",   "http://127.0.0.1:4000");
    if (opt.endpoint.empty())
        opt.endpoint = getConfigOrEnv(config_nl2smt, "api_base", "OPENAI_API_BASE",   "http://127.0.0.1:4000");
    opt.path       = getConfigOrEnv(config_nl2smt, "path",      nullptr,             "/v1/chat/completions");
    opt.model      = getConfigOrEnv(config_nl2smt, "model",      "NL2SMT_MODEL",      "openai/gpt-4o-mini");
    opt.temperature= getConfigDouble(config_nl2smt, "temperature", 0.0);
    opt.timeout_sec= getConfigInt(config_nl2smt, "timeout_sec", 90);
    // max_repair: used by library in parseNL (parse+repair step for both Structured and DirectTextual: src/nl2smt.cpp parseSmt2WithRepair)
    opt.max_repair = cli.no_repair ? 0 : (cli.max_repair >= 0 ? cli.max_repair : getConfigInt(config_nl2smt, "max_repair", 3));
    opt.prompt_ld_path    = getConfigOrEnv(config_nl2smt, "prompt_ld",   "NL2SMT_PROMPT_LD",   "");
    opt.prompt_apt_path   = getConfigOrEnv(config_nl2smt, "prompt_apt",  "NL2SMT_PROMPT_APT",  "");
    opt.prompt_repair_path= getConfigOrEnv(config_nl2smt, "prompt_repair","NL2SMT_PROMPT_REPAIR","");
    opt.prompt_legacy_path= getConfigOrEnv(config_nl2smt, "prompt_file",  "NL2SMT_PROMPT_FILE",  "");
    opt.artifact_dir = cli.artifact_dir.empty()
        ? getConfigOrEnv(config_nl2smt, "artifact_dir", nullptr, "") : cli.artifact_dir;
    opt.quiet = cli.quiet;
    std::string strategyStr = getConfigOrEnv(config_nl2smt, "strategy", nullptr, "Structured");
    if (!cli.strategy_override.empty()) strategyStr = cli.strategy_override;
    opt.strategy = strategyFromString(strategyStr);
    return opt;
}

bool runParseNL(Parser* parser, const std::string& nl,
                const smtlib::NL2SMTOptions& opt,
                smtlib::NL2SMTReport* report) {
    if (!parser) return false;
    return parser->parseNL(nl, opt, report);
}

}  // namespace NL2SMT
}  // namespace SMTParser

#endif  /* BUILD_NL2SMT && SMTLIBPARSER_ENABLE_NL2SMT */
