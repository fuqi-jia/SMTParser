/* -*- Header -*-
 * NL2SMT app: build options from config/CLI and call Parser::parseNL (library).
 */
#ifndef APPS_NL2SMT_RUN_NL2SMT_HEADER
#define APPS_NL2SMT_RUN_NL2SMT_HEADER

#if !defined(BUILD_NL2SMT) || !defined(SMTLIBPARSER_ENABLE_NL2SMT)
#error "nl2smt/run_nl2smt.h requires BUILD_NL2SMT and SMTLIBPARSER_ENABLE_NL2SMT"
#endif

#include "parser.h"  /* includes nl2smt.h → smtlib::NL2SMTOptions, NL2SMTReport */

#include <map>
#include <string>

namespace SMTParser {
namespace NL2SMT {

/** CLI overrides for NL mode (from --nl-* and --quiet). */
struct NLCliOverrides {
    std::string artifact_dir;
    std::string strategy_override;  /**< e.g. "DirectTextual"; empty = use config/default */
    int max_repair = 3;
    bool no_repair = false;
    bool quiet = false;
};

/**
 * Build smtlib::NL2SMTOptions from config [nl2smt] map and CLI overrides.
 * Config keys: endpoint, path, model, temperature, timeout_sec, max_repair,
 *   strategy, prompt_ld, prompt_apt, prompt_repair, prompt_direct, artifact_dir, quiet.
 * Env (if set) can override: NL2SMT_API_KEY/OPENAI_API_KEY used by library; optional NL2SMT_ENDPOINT, etc.
 */
smtlib::NL2SMTOptions buildOptions(
    const std::map<std::string, std::string>& config_nl2smt,
    const NLCliOverrides& cli);

/**
 * Run NL -> DAG via Parser::parseNL. Returns true on success.
 * On failure, report->last_error is set.
 */
bool runParseNL(Parser* parser, const std::string& nl,
                const smtlib::NL2SMTOptions& opt,
                smtlib::NL2SMTReport* report);

}  // namespace NL2SMT
}  // namespace SMTParser

#endif
