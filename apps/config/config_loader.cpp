/* -*- Source -*-
 * Unified config: load file (sections [parser], [nl2smt], [solver]) and apply to parser + env.
 */
#include "config/config_loader.h"
#include "parser.h"
#include <fstream>
#include <cstdlib>
#include <cstring>

#if !defined(_WIN32) && !defined(_WIN64)
#include <stdlib.h>
#endif

namespace SMTParser {
namespace App {

static void trim(std::string& s) {
    s.erase(0, s.find_first_not_of(" \t"));
    s.erase(s.find_last_not_of(" \t") + 1);
}

bool loadConfigFile(const std::string& path, AppConfig* config) {
    if (!config) return false;
    std::ifstream f(path);
    if (!f) return false;
    std::string line;
    std::string section;
    while (std::getline(f, line)) {
        size_t c = line.find('#');
        if (c != std::string::npos) line = line.substr(0, c);
        trim(line);
        if (line.empty()) continue;
        if (line.size() >= 2 && line.front() == '[' && line.back() == ']') {
            section = line.substr(1, line.size() - 2);
            trim(section);
            continue;
        }
        size_t eq = line.find('=');
        if (eq == std::string::npos) continue;
        std::string key = line.substr(0, eq);
        std::string val = line.substr(eq + 1);
        trim(key);
        trim(val);
        if (section == "parser" || section.empty())
            config->parser[key] = val;
        else if (section == "nl2smt")
            config->nl2smt[key] = val;
        else if (section == "solver") {
            if (key == "path")
                config->solver_path = val;
        }
    }
    return true;
}

void applyArgs(int argc, char* argv[], AppConfig* config) {
    if (!config) return;
    for (int i = 0; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--logic" && i + 1 < argc) {
            config->parser["logic"] = argv[++i];
            continue;
        }
        if (a.find("--option=") == 0) {
            std::string rest = a.substr(9);
            size_t eq = rest.find('=');
            if (eq != std::string::npos)
                config->parser[rest.substr(0, eq)] = rest.substr(eq + 1);
            continue;
        }
        if (a == "--solver" && i + 1 < argc) {
            config->solver_path = argv[++i];
            continue;
        }
    }
}

void applyParserConfig(SMTParser::Parser* parser, const std::map<std::string, std::string>& parser_opts) {
    if (!parser) return;
    for (const auto& kv : parser_opts)
        parser->setOption(kv.first, kv.second);
}

void applyNl2smtEnv(const std::map<std::string, std::string>& nl2smt_opts) {
    for (const auto& kv : nl2smt_opts) {
        if (kv.first.empty()) continue;
#ifdef _WIN32
        _putenv_s(kv.first.c_str(), kv.second.c_str());
#else
        setenv(kv.first.c_str(), kv.second.c_str(), 1);
#endif
    }
}

}  // namespace App
}  // namespace SMTParser
