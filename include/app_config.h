/* -*- Header -*-
 * Unified config (library): parser, nl2smt, solver.
 * Config file: sections [parser], [nl2smt], [solver]; key=value per line, # comment.
 */
#ifndef SMTPARSER_APP_CONFIG_HEADER
#define SMTPARSER_APP_CONFIG_HEADER

#include <map>
#include <string>

namespace SMTParser {
class Parser;
namespace App {

struct AppConfig {
    std::map<std::string, std::string> parser;
    std::map<std::string, std::string> nl2smt;
    std::string solver_path;
};

bool loadConfigFile(const std::string& path, AppConfig* config);
std::string findDefaultConfigPath();
void applyArgs(int argc, char* argv[], AppConfig* config);
void applyParserConfig(SMTParser::Parser* parser, const std::map<std::string, std::string>& parser_opts);
void applyNl2smtEnv(const std::map<std::string, std::string>& nl2smt_opts);

}  // namespace App
}  // namespace SMTParser

#endif
