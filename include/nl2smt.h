/* -*- Header -*-
 * NL2SMT: Natural language -> Structured (LD+APT+Builder) or DirectTextual -> DAG
 * Options and report for Parser::parseNL(). Only relevant when SMTLIBPARSER_ENABLE_NL2SMT is defined.
 */
#ifndef NL2SMT_HEADER
#define NL2SMT_HEADER

#include <string>

namespace smtlib {

/** Compilation strategy for parseNL. */
enum class NLCompilationStrategy {
    /** Logical Decomposition + Atomic Proposition Translation + Builder (semantic compiler path). */
    Structured,
    /** End-to-end text: NL -> LLM -> SMT2 -> Parse (baseline). */
    DirectTextual
};

/** Options for parseNL (LiteLLM Proxy / OpenAI-compatible HTTP). */
struct NL2SMTOptions {
    std::string endpoint = "http://127.0.0.1:4000";
    std::string path     = "/v1/chat/completions";
    std::string model    = "openai/gpt-4o-mini";
    double temperature   = 0.0;
    int timeout_sec      = 90;
    int max_repair       = 3;

    NLCompilationStrategy strategy = NLCompilationStrategy::Structured;

    std::string prompt_ld_path;
    std::string prompt_apt_path;
    std::string prompt_repair_path;
    std::string prompt_direct_path;

    std::string artifact_dir;
    bool dump_smt2 = true;
    bool quiet     = false;
};

/** Report from parseNL. */
struct NL2SMTReport {
    bool ok           = false;
    int repair_rounds = 0;
    std::string plan_json;
    std::string smt2;
    std::string last_error;
    std::string artifacts_dir_used;
};

} // namespace smtlib

#endif
