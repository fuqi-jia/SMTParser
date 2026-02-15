/* -*- Source -*-
 * smtparser: unified main — feature (syntax features), solver, nl (natural language → SMT)
 */
#include "app_config.h"
#include "parser.h"
#include "features/run_features.h"
#include "solver/run_solver.h"
#include "parser.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <cstdlib>
#include <cstdio>

#if defined(BUILD_NL2SMT)
#include "nl2smt/run_nl2smt.h"
#endif

#if !defined(_WIN32) && !defined(_WIN64)
#include <unistd.h>
#endif

static void usage(const char* prog) {
    std::cerr << "smtparser — unified CLI (feature / solve / nl)\n\n";

    std::cerr << "Subcommands:\n"
              << "  feature [options] <file.smt2>  Parse SMT file and print syntax features.\n"
              << "  solve [options] [file.smt2]     Run external solver on file (requires solver path).\n"
#if defined(BUILD_NL2SMT)
              << "  nl [options] <file|string>      Natural language → DAG (Parser::parseNL, LiteLLM Proxy).\n"
              << "  (nl options: --nl-no-repair, --nl-max-repair=N, --nl-artifact-dir=DIR, --nl-strategy=Structured|DirectTextual, --quiet)\n"
#endif
              << "  [options] <file.smt2>           Default: same as feature.\n\n";

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

    std::cerr << "  [nl2smt]  — NL2SMT (Parser::parseNL, LiteLLM Proxy)\n"
              << "    endpoint / api_base             Proxy URL (default: http://127.0.0.1:4000).\n"
              << "    path                            API path (default: /v1/chat/completions).\n"
              << "    model / NL2SMT_MODEL            Model name (default: openai/gpt-4o-mini).\n"
              << "    api_key / OPENAI_API_KEY        API key (or NL2SMT_API_KEY).\n"
              << "    prompt_ld, prompt_apt, prompt_repair, prompt_direct  Prompt file paths.\n\n";

    std::cerr << "  [solver]  — solver mode\n"
              << "    solver.path                       Path to SMT solver executable (e.g. /usr/bin/z3).\n\n";

    std::cerr << "Examples:\n"
              << "  " << prog << " --config my.conf feature foo.smt2\n"
              << "  " << prog << " solve --solver /usr/bin/z3 foo.smt2\n"
#if defined(BUILD_NL2SMT)
              << "  " << prog << " nl \"maximize x + y under x >= 0, y >= 0\"\n"
#endif
              << "  " << prog << " --option logic=QF_LRA feature foo.smt2\n";
}

int main(int argc, char* argv[]) {
    const char* configPath = nullptr;
    std::string subcommand;
    std::string smtFile;
    std::string nlInput;
    bool hasNl = false;
#if defined(BUILD_NL2SMT)
    bool nlNoRepair = false;
    int nlMaxRepair = 3;
    std::string nlArtifactDir;
    std::string nlStrategyOverride;
    bool nlQuiet = false;
#endif

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--config" && i + 1 < argc) { configPath = argv[++i]; continue; }
        if (a == "--solver" && i + 1 < argc) { (void)argv[++i]; continue; }
#if defined(BUILD_NL2SMT)
        if (a == "--nl-no-repair") { nlNoRepair = true; continue; }
        if (a.compare(0, 15, "--nl-max-repair=") == 0) {
            nlMaxRepair = std::atoi(a.c_str() + 15);
            if (nlMaxRepair < 0) nlMaxRepair = 0;
            continue;
        }
        if (a.compare(0, 19, "--nl-artifact-dir=") == 0) { nlArtifactDir = a.substr(19); continue; }
        if (a.compare(0, 14, "--nl-strategy=") == 0) { nlStrategyOverride = a.substr(14); continue; }
        if (a == "--nl-strategy" && i + 1 < argc) { nlStrategyOverride = argv[++i]; continue; }
        if (a == "--quiet") { nlQuiet = true; continue; }
#endif
        if (a == "--logic" || a == "--option" || (a.size() > 1 && a[0] == '-')) continue;
        if (a == "feature" || a == "solve") {
            subcommand = a;
            continue;
        }
        if (a == "nl") {
            if (subcommand.empty())
                subcommand = "nl";
            else if (subcommand == "solve")
                smtFile = "nl";
            continue;
        }
        if (!a.empty() && a[0] != '-') {
            if (subcommand == "nl")
                nlInput = a;
            else if (subcommand == "solve" && smtFile == "nl")
                nlInput = a, smtFile.clear(), hasNl = true;
            else
                smtFile = a;
        }
    }
    if (subcommand.empty() && !smtFile.empty()) subcommand = "feature";
    if (subcommand == "solve" && smtFile == "nl" && !nlInput.empty())
        smtFile.clear(), hasNl = true;
    if (subcommand.empty() && !smtFile.empty()) subcommand = "feature";

    /* Resolve nl input: strip quotes or read from file */
#if defined(BUILD_NL2SMT)
    if (subcommand == "nl" || hasNl) {
        if (!nlInput.empty()) {
            if (nlInput.size() >= 2 && nlInput.front() == '"' && nlInput.back() == '"')
                nlInput = nlInput.substr(1, nlInput.size() - 2);
            else if (nlInput.find('"') == std::string::npos) {
                std::ifstream f(nlInput);
                if (f) { std::ostringstream os; os << f.rdbuf(); nlInput = os.str(); }
            }
        }
    }
#endif

    SMTParser::App::AppConfig config;
    bool configLoaded = false;
    if (configPath) {
        configLoaded = SMTParser::App::loadConfigFile(configPath, &config);
    } else {
        std::string defPath = SMTParser::App::findDefaultConfigPath();
        if (!defPath.empty())
            configLoaded = SMTParser::App::loadConfigFile(defPath, &config);
    }
    SMTParser::App::applyArgs(argc, argv, &config);

    auto parser = SMTParser::newParser();
    SMTParser::App::applyParserConfig(parser.get(), config.parser);
    SMTParser::App::applyNl2smtEnv(config.nl2smt);

    if (subcommand == "feature") {
        if (smtFile.empty()) {
            std::cerr << "Error: feature requires <file.smt2>.\n";
            usage(argv[0]);
            return 1;
        }
        return SMTParser::App::runFeatures(smtFile.c_str());
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
#if defined(BUILD_NL2SMT) && defined(SMTLIBPARSER_ENABLE_NL2SMT)
            if (!configLoaded) {
                std::cerr << "未找到 NL2SMT 配置。请复制 .config/llm.conf.example 为 .config/llm.conf 并编辑。\n";
                return 1;
            }
            SMTParser::NL2SMT::NLCliOverrides cli;
            cli.artifact_dir = nlArtifactDir;
            cli.strategy_override = nlStrategyOverride;
            cli.max_repair = nlMaxRepair;
            cli.no_repair = nlNoRepair;
            cli.quiet = nlQuiet;
            smtlib::NL2SMTOptions opt = SMTParser::NL2SMT::buildOptions(config.nl2smt, cli);
            smtlib::NL2SMTReport report;
            if (!SMTParser::NL2SMT::runParseNL(parser.get(), nlInput, opt, &report)) {
                std::cerr << "NL2SMT error: " << report.last_error << std::endl;
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
            std::cerr << "Error: solve nl requires BUILD_NL2SMT. Use file.smt2.\n";
            return 1;
#endif
        }
        if (pathToRun.empty()) {
            std::cerr << "Error: provide file.smt2 or solve nl \"...\".\n";
            SMTParser::App::printSolverUsage(argv[0]);
            return 1;
        }
        int ret = SMTParser::App::runSolver(config.solver_path, pathToRun);
        if (!tempPath.empty()) std::remove(tempPath.c_str());
        return ret >= 0 ? ret : 1;
    }

    if (subcommand == "nl") {
#if defined(BUILD_NL2SMT) && defined(SMTLIBPARSER_ENABLE_NL2SMT)
        if (nlInput.empty()) {
            std::cerr << "Error: nl requires <file> or <string>.\n";
            usage(argv[0]);
            return 1;
        }
        if (!configLoaded) {
            std::cerr << "未找到 NL2SMT 配置。请复制 .config/llm.conf.example 为 .config/llm.conf 并编辑。\n";
            return 1;
        }
        SMTParser::NL2SMT::NLCliOverrides cli;
        cli.artifact_dir = nlArtifactDir;
        cli.strategy_override = nlStrategyOverride;
        cli.max_repair = nlMaxRepair;
        cli.no_repair = nlNoRepair;
        cli.quiet = nlQuiet;
        smtlib::NL2SMTOptions opt = SMTParser::NL2SMT::buildOptions(config.nl2smt, cli);
        smtlib::NL2SMTReport report;
        if (!SMTParser::NL2SMT::runParseNL(parser.get(), nlInput, opt, &report)) {
            std::cerr << "NL2SMT error: " << report.last_error << std::endl;
            if (!report.debug_info.empty()) std::cerr << "  debug: " << report.debug_info << std::endl;
            return 1;
        }
        if (!nlQuiet) {
            size_t nAst = parser->getAssertions().size();
            size_t nObj = parser->getObjectives().size();
            std::string logicStr = parser->getOptions() && parser->getOptions()->getLogic() != "" ? parser->getOptions()->getLogic() : "UNKNOWN_LOGIC";
            std::cerr << "NL2SMT: strategy=" << (opt.strategy == smtlib::NLCompilationStrategy::DirectTextual ? "DirectTextual" : "Structured")
                      << " logic=" << logicStr
                      << " assertions=" << nAst << " objectives=" << nObj << " repair_rounds=" << report.repair_rounds;
            if (!report.artifacts_dir_used.empty()) std::cerr << " artifacts=" << report.artifacts_dir_used;
            if (!report.debug_info.empty()) std::cerr << " | " << report.debug_info;
            std::cerr << std::endl;
        }
        std::cout << parser->dumpSMT2() << std::endl;
        return 0;
#else
        std::cerr << "Error: nl subcommand requires BUILD_NL2SMT.\n";
        return 1;
#endif
    }

    usage(argv[0]);
    return 0;
}
