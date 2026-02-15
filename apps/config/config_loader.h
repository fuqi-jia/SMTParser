/* -*- Header -*-
 * Unified config: all settings for parser + apps (nl2smt, solver).
 * Config file: sections [parser], [nl2smt], [solver]; key=value per line, # comment.
 * CLI overrides: --config, --logic, --option K=V, --solver PATH (main passes argv to applyArgs).
 * Parser options (options.h) are applied from config.parser; options stay parser-internal.
 */
#ifndef APPS_CONFIG_LOADER_HEADER
#define APPS_CONFIG_LOADER_HEADER

#include <map>
#include <string>

namespace SMTParser {
class Parser;
namespace App {

/** Unified config: parser options, nl2smt options, solver path. */
struct AppConfig {
    std::map<std::string, std::string> parser;
    std::map<std::string, std::string> nl2smt;
    std::string solver_path;
};

/** Load config file into config. Sections: [parser], [nl2smt], [solver]. */
bool loadConfigFile(const std::string& path, AppConfig* config);

/**
 * Default config search order (when --config not given):
 * 1) ./smtparser.conf
 * 2) ./.config/llm.conf   (project-local)
 * 3) ~/.config/smtparser/llm.conf  (Linux/macOS user)
 * Returns first path that exists and is readable; empty string if none.
 */
std::string findDefaultConfigPath();

/** Parse argv and override config: --logic X, --option K=V (parser), --solver PATH. */
void applyArgs(int argc, char* argv[], AppConfig* config);

/** Apply config.parser to parser (setOption for each key=value). */
void applyParserConfig(SMTParser::Parser* parser, const std::map<std::string, std::string>& parser_opts);

/** Set environment variables from nl2smt options (keys = env names, e.g. NL2SMT_LLM_SCRIPT). */
void applyNl2smtEnv(const std::map<std::string, std::string>& nl2smt_opts);

}  // namespace App
}  // namespace SMTParser

#endif
