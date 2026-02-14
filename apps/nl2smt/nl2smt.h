/* -*- Header -*-
 * NL2SMT compiler: Natural Language -> Tree-Plan -> Emit -> (Parse | Repair loop) -> SMTParser DAG
 */
#ifndef NL2SMT_NL2SMT_HEADER
#define NL2SMT_NL2SMT_HEADER

#include "parser.h"
#include <memory>
#include <string>

namespace SMTParser {
namespace NL2SMT {

/** Options for Tree-Plan -> Emit -> Repair pipeline. */
struct NL2SMTOptions {
    bool plan_only = false;      /**< If true, run plan phase only and report plan JSON (no emit/parse). */
    bool no_repair = false;      /**< If true, do not run repair loop on parse failure. */
    int max_repair = 3;          /**< Max repair attempts after parse failure (0 = no repair). */
    bool no_typecheck = false;   /**< If true, skip lightweight sort/arity checks in plan (default: typecheck on, failures trigger repair). */
    std::string artifact_dir;    /**< If non-empty, write nl.txt, plan.json, emit.smt2, parse_error.txt, repair_*.smt2 for debugging. */
    bool keep_tmp = false;       /**< If true, do not remove temporary .smt2 files. */
    bool roundtrip_check = false; /**< If true, after parse verify parse(dump(parse(emit(plan)))) succeeds. */
    bool fallback_cmd = false;   /**< If true, when SCRIPT is set but fails, fall back to CMD (default: no fallback). */
    bool quiet = false;          /**< If true, do not print assumption/summary (used by main for --quiet). */
};

class NL2SMTCompiler {
public:
    explicit NL2SMTCompiler(std::shared_ptr<Parser> parser);

    /** Set options for plan-only / no-repair / max-repair. */
    void setOptions(const NL2SMTOptions& opts) { options_ = opts; }
    NL2SMTOptions& options() { return options_; }
    const NL2SMTOptions& options() const { return options_; }

    /**
     * Compile: NL -> Plan (JSON) -> Emit (SMT-LIB2) -> Parse; on parse failure optionally Repair loop.
     * If plan_only: run plan only, put plan JSON in report() and return true.
     */
    bool compile(const std::string& text);

    /** Last error/warning message, or plan JSON when plan_only succeeded. */
    std::string report() const { return report_; }

    /** Number of repair rounds used in last successful compile (0 = no repair). Only valid after compile() returns true. */
    int lastRepairCount() const { return last_repair_count_; }

private:
    /** Best-effort validation: required keys, var∈symbols, and optionally lightweight arity/sort checks. */
    static bool validatePlan(const std::string& planJson, bool doTypecheck);

    /** Lightweight arity check: not→1, and/or→≥1, implies→2, ite→3, comparisons→2, +-*→≥2. */
    static bool validatePlanArity(const std::string& planJson);

    std::shared_ptr<Parser> parser_;
    NL2SMTOptions options_;
    mutable std::string report_;
    int last_repair_count_ = -1;
};

}  // namespace NL2SMT
}  // namespace SMTParser

#endif
