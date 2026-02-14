/* -*- Source -*-
 * smtparser: unified main — parser (stats), solver (run external solver), nl (natural language → SMT)
 */
#include "main.h"
#include "config/config_loader.h"
#include "parser/run_parser.h"
#include "solver/run_solver.h"
#include "parser.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <cstdlib>
#include <cstdio>

#if defined(BUILD_NL2SMT)
#include "nl2smt/nl2smt.h"
#endif

#if !defined(_WIN32) && !defined(_WIN64)
#include <unistd.h>
#endif

static void usage(const char* prog) {
    std::cerr << "smtparser — unified CLI (parse / solve / nl)\n\n";

    std::cerr << "Subcommands:\n"
              << "  parse [options] <file.smt2>     Parse SMT file and print statistics.\n"
              << "  solve [options] [file.smt2]     Run external solver on file (requires solver path).\n"
#if defined(BUILD_NL2SMT)
              << "  --nl <file|string>               Natural language → SMT-LIB2 (Tree-Plan→Emit→Repair).\n"
              << "  --nl-plan-only                   Only output JSON plan (no emit/parse).\n"
              << "  --nl-no-repair                   Do not run repair loop on parse failure.\n"
              << "  --nl-max-repair=N                Max repair attempts (default: 3).\n"
              << "  --nl-no-typecheck                Disable plan arity/sort checks (default: on).\n"
              << "  --nl-artifact-dir=DIR            Write nl.txt, plan.json, emit.smt2, repair_*.smt2 for debugging.\n"
              << "  --nl-keep-tmp                    Keep temporary .smt2 files.\n"
              << "  --nl-roundtrip-check             Verify parse(dump(parse(emit(plan)))) succeeds.\n"
              << "  --nl-fallback-cmd                On SCRIPT failure, fall back to CMD (default: no).\n"
              << "  --quiet                          Suppress NL2SMT summary (assertions/objectives/repair count).\n"
#endif
              << "  [options] <file.smt2>           Default: same as parse.\n\n";

    std::cerr << "CLI options (override config file):\n"
              << "  --config PATH    Load unified config from PATH (sections [parser], [nl2smt], [solver]).\n"
              << "  --option K=V     Parser option (K = parser.* key, e.g. logic=QF_LRA). Can repeat.\n"
              << "  --solver PATH    Solver executable path. Same as solver.path.\n\n";

    std::cerr << "Config file (--config PATH): key=value per line, # comment.\n"
              << "Use section [parser], [nl2smt], or [solver]; key below = name in that section (no prefix).\n\n";

    std::cerr << "  [parser]  — parser options (see include/options.h)\n"
              << "    parser.logic                      SMT-LIB logic (default: UNKNOWN_LOGIC).\n"
              << "    parser.keep_let                   Preserve let-bindings (true|false, default: true).\n"
              << "    parser.keep_division              Keep division if not divisible (true|false, default: true).\n"
              << "    parser.precision                   MPFR precision in bits (default: 128).\n"
              << "    parser.float_evaluate             Use floating-point evaluation (true|false, default: true).\n"
              << "    parser.expand_functions            Inline define-fun (true|false, default: true).\n"
              << "    parser.expand_recursive_functions  Expand define-fun-rec (true|false, default: false).\n\n";

    std::cerr << "  [nl2smt]  — NL2SMT (env names; overridden by real environment)\n"
              << "    nl2smt.NL2SMT_LLM_SCRIPT         Path to llm_call.py (or use NL2SMT_LLM_CMD).\n"
              << "    nl2smt.NL2SMT_LLM_CMD            Full command for LLM (app receives temp file path).\n"
              << "    nl2smt.OPENAI_API_KEY            API key for OpenAI-compatible service.\n"
              << "    nl2smt.OPENAI_API_BASE           Optional API base URL.\n"
              << "    nl2smt.NL2SMT_MODEL              Model name (default: gpt-4o-mini).\n"
              << "    nl2smt.NL2SMT_PROMPT_FILE        Optional path to system prompt file (legacy).\n"
              << "    nl2smt.NL2SMT_PROMPT_PLAN/EMIT/REPAIR  Three-phase prompt files.\n\n";

    std::cerr << "  [solver]  — solver mode\n"
              << "    solver.path                       Path to SMT solver executable (e.g. /usr/bin/z3).\n\n";

    std::cerr << "Examples:\n"
              << "  " << prog << " --config my.conf parse foo.smt2\n"
              << "  " << prog << " solve --solver /usr/bin/z3 foo.smt2\n"
#if defined(BUILD_NL2SMT)
              << "  " << prog << " --nl \"maximize x + y under x >= 0, y >= 0\"\n"
#endif
              << "  " << prog << " --option logic=QF_LRA parse foo.smt2\n";
}

int main(int argc, char* argv[]) {
    const char* configPath = nullptr;
    std::string subcommand;
    std::string smtFile;
    std::string nlInput;
    bool hasNl = false;
#if defined(BUILD_NL2SMT)
    bool nlPlanOnly = false;
    bool nlNoRepair = false;
    int nlMaxRepair = 3;
    bool nlNoTypecheck = false;
    std::string nlArtifactDir;
    bool nlKeepTmp = false;
    bool nlRoundtripCheck = false;
    bool nlFallbackCmd = false;
    bool nlQuiet = false;
#endif

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--config" && i + 1 < argc) { configPath = argv[++i]; continue; }
        if (a == "--solver" && i + 1 < argc) { (void)argv[++i]; continue; }
        if (a == "--nl") {
            hasNl = true;
            if (i + 1 < argc) {
                nlInput = argv[++i];
                if (nlInput.size() >= 2 && nlInput.front() == '"' && nlInput.back() == '"')
                    nlInput = nlInput.substr(1, nlInput.size() - 2);
                else if (nlInput.find('"') == std::string::npos) {
                    std::ifstream f(nlInput);
                    if (f) { std::ostringstream os; os << f.rdbuf(); nlInput = os.str(); }
                }
            }
            continue;
        }
#if defined(BUILD_NL2SMT)
        if (a == "--nl-plan-only") { nlPlanOnly = true; continue; }
        if (a == "--nl-no-repair") { nlNoRepair = true; continue; }
        if (a.compare(0, 15, "--nl-max-repair=") == 0) {
            nlMaxRepair = std::atoi(a.c_str() + 15);
            if (nlMaxRepair < 0) nlMaxRepair = 0;
            continue;
        }
        if (a == "--nl-no-typecheck") { nlNoTypecheck = true; continue; }
        if (a.compare(0, 19, "--nl-artifact-dir=") == 0) { nlArtifactDir = a.substr(19); continue; }
        if (a == "--nl-keep-tmp") { nlKeepTmp = true; continue; }
        if (a == "--nl-roundtrip-check") { nlRoundtripCheck = true; continue; }
        if (a == "--nl-fallback-cmd") { nlFallbackCmd = true; continue; }
        if (a == "--quiet") { nlQuiet = true; continue; }
#endif
        if (a == "--logic" || a == "--option" || (a.size() > 1 && a[0] == '-')) continue;
        if (a == "parse" || a == "solve") {
            subcommand = a;
            continue;
        }
        if (!a.empty() && a[0] != '-') smtFile = a;
    }
    if (subcommand.empty() && !smtFile.empty()) subcommand = "parse";
    if (subcommand.empty() && hasNl) subcommand = "nl";
    if (subcommand.empty() && !smtFile.empty()) subcommand = "parse";

    SMTParser::App::AppConfig config;
    if (configPath) SMTParser::App::loadConfigFile(configPath, &config);
    SMTParser::App::applyArgs(argc, argv, &config);

    auto parser = SMTParser::newParser();
    SMTParser::App::applyParserConfig(parser.get(), config.parser);
    SMTParser::App::applyNl2smtEnv(config.nl2smt);

    if (subcommand == "parse") {
        if (smtFile.empty()) {
            std::cerr << "Error: parse requires <file.smt2>.\n";
            usage(argv[0]);
            return 1;
        }
        return SMTParser::App::runParser(smtFile.c_str());
    }

    if (subcommand == "solve") {
        if (config.solver_path.empty()) {
            std::cerr << "Error: solve requires --solver <path> (or solver.path in config).\n";
            SMTParser::App::printSolverUsage(argv[0]);
            return 1;
        }
        std::string pathToRun = smtFile;
        std::string tempPath;
        if (pathToRun.empty() && hasNl && !nlInput.empty()) {
#if defined(BUILD_NL2SMT)
            SMTParser::NL2SMT::NL2SMTCompiler compiler(parser);
            compiler.options().plan_only = nlPlanOnly;
            compiler.options().no_repair = nlNoRepair;
            compiler.options().max_repair = nlMaxRepair;
            compiler.options().no_typecheck = nlNoTypecheck;
            compiler.options().artifact_dir = nlArtifactDir;
            compiler.options().keep_tmp = nlKeepTmp;
            compiler.options().roundtrip_check = nlRoundtripCheck;
            compiler.options().fallback_cmd = nlFallbackCmd;
            compiler.options().quiet = nlQuiet;
            if (!compiler.compile(nlInput)) {
                std::cerr << "NL2SMT error: " << compiler.report() << std::endl;
                return 1;
            }
            const char* tmpDir = std::getenv("TMPDIR");
            if (!tmpDir) tmpDir = std::getenv("TEMP");
            if (!tmpDir) tmpDir = "/tmp";
            tempPath = std::string(tmpDir) + "/smtparser_solve_";
#ifdef _WIN32
            tempPath += "0";
#else
            tempPath += std::to_string(static_cast<long>(getpid()));
#endif
            tempPath += ".smt2";
            std::ofstream of(tempPath);
            if (!of) { std::cerr << "Cannot write temp file.\n"; return 1; }
            of << parser->dumpSMT2();
            of.close();
            pathToRun = tempPath;
#else
            std::cerr << "Error: --nl in solve mode requires BUILD_NL2SMT. Use file.smt2.\n";
            return 1;
#endif
        }
        if (pathToRun.empty()) {
            std::cerr << "Error: provide file.smt2 or --nl \"...\".\n";
            SMTParser::App::printSolverUsage(argv[0]);
            return 1;
        }
        int ret = SMTParser::App::runSolver(config.solver_path, pathToRun);
        if (!tempPath.empty()) std::remove(tempPath.c_str());
        return ret >= 0 ? ret : 1;
    }

    if (subcommand == "nl") {
#if defined(BUILD_NL2SMT)
        if (nlInput.empty()) {
            std::cerr << "Error: --nl requires a file path or quoted string.\n";
            usage(argv[0]);
            return 1;
        }
        SMTParser::NL2SMT::NL2SMTCompiler compiler(parser);
        compiler.options().plan_only = nlPlanOnly;
        compiler.options().no_repair = nlNoRepair;
        compiler.options().max_repair = nlMaxRepair;
        compiler.options().no_typecheck = nlNoTypecheck;
        compiler.options().artifact_dir = nlArtifactDir;
        compiler.options().keep_tmp = nlKeepTmp;
        compiler.options().roundtrip_check = nlRoundtripCheck;
        compiler.options().fallback_cmd = nlFallbackCmd;
        compiler.options().quiet = nlQuiet;
        if (!compiler.compile(nlInput)) {
            std::cerr << "NL2SMT error: " << compiler.report() << std::endl;
            return 1;
        }
        if (nlPlanOnly) {
            std::cout << compiler.report() << std::endl;
        } else {
            if (!nlQuiet) {
                size_t nAst = parser->getAssertions().size();
                size_t nObj = parser->getObjectives().size();
                int repairs = compiler.lastRepairCount() >= 0 ? compiler.lastRepairCount() : 0;
                std::cerr << "NL2SMT: assertions=" << nAst << " objectives=" << nObj << " repair_rounds=" << repairs;
                if (!nlArtifactDir.empty()) std::cerr << " artifacts=" << nlArtifactDir;
                std::cerr << std::endl;
            }
            std::cout << parser->dumpSMT2() << std::endl;
        }
        return 0;
#else
        std::cerr << "Error: --nl requires BUILD_NL2SMT.\n";
        return 1;
#endif
    }

    usage(argv[0]);
    return 0;
}
