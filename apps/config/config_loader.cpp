/* -*- Source -*-
 * Unified config: load file (sections [parser], [nl2smt], [solver]) and apply to parser + env.
 * [nl2smt]: short keys (model, api_key, prompt_plan, ...) are mapped to env names when applying.
 * Relative prompt paths in [nl2smt] are resolved against the config file's directory.
 */
#include "config/config_loader.h"
#include "parser.h"
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <string>

#if defined(_WIN32) || defined(_WIN64)
#include <direct.h>
#include <io.h>
#else
#include <stdlib.h>
#include <unistd.h>
#endif

namespace SMTParser {
namespace App {

static void trim(std::string& s) {
    s.erase(0, s.find_first_not_of(" \t"));
    s.erase(s.find_last_not_of(" \t") + 1);
}

/** Return true if path exists and is readable (file). */
static bool fileExists(const std::string& path) {
    std::ifstream f(path);
    return f.good();
}

/** True if path looks absolute (Unix / or Windows C:). */
static bool isAbsolutePath(const std::string& path) {
    if (path.empty()) return false;
    if (path[0] == '/') return true;
#if defined(_WIN32) || defined(_WIN64)
    if (path.size() >= 2 && path[1] == ':') return true;
#endif
    return false;
}

/** [nl2smt] keys whose values are prompt file paths (relative → resolve against config dir). */
static bool isPromptPathKey(const std::string& key) {
    return key == "prompt_file" || key == "prompt_plan" || key == "prompt_emit" || key == "prompt_repair"
        || key == "NL2SMT_PROMPT_FILE" || key == "NL2SMT_PROMPT_PLAN"
        || key == "NL2SMT_PROMPT_EMIT" || key == "NL2SMT_PROMPT_REPAIR";
}

bool loadConfigFile(const std::string& path, AppConfig* config) {
    if (!config) return false;
    std::ifstream f(path);
    if (!f) return false;
    std::string configDir;
    {
        size_t last = path.find_last_of("/\\");
        if (last != std::string::npos)
            configDir = path.substr(0, last + 1);
        else
            configDir = "./";
    }
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
        if (section == "nl2smt" && isPromptPathKey(key) && !val.empty() && !isAbsolutePath(val))
            val = configDir + val;
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

std::string findDefaultConfigPath() {
    if (fileExists("smtparser.conf"))
        return "smtparser.conf";
    if (fileExists(".config/llm.conf"))
        return ".config/llm.conf";
#if !defined(_WIN32) && !defined(_WIN64)
    const char* home = getenv("HOME");
    if (home && *home) {
        std::string p = std::string(home) + "/.config/smtparser/llm.conf";
        if (fileExists(p)) return p;
    }
#endif
    return std::string();
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

/** Map [nl2smt] short key to env var name; empty string = use key as-is. */
static const char* nl2smtKeyToEnv(const std::string& key) {
    if (key == "model") return "NL2SMT_MODEL";
    if (key == "api_key") return "OPENAI_API_KEY";
    if (key == "api_base") return "OPENAI_API_BASE";
    if (key == "provider") return "NL2SMT_PROVIDER";
    if (key == "temperature") return "NL2SMT_TEMPERATURE";
    if (key == "timeout_sec") return "NL2SMT_TIMEOUT_SEC";
    if (key == "use_responses") return "NL2SMT_USE_RESPONSES";
    if (key == "reasoning_effort") return "NL2SMT_REASONING_EFFORT";
    if (key == "max_retries") return "NL2SMT_MAX_RETRIES";
    if (key == "debug") return "NL2SMT_DEBUG";
    if (key == "prompt_file") return "NL2SMT_PROMPT_FILE";
    if (key == "prompt_plan") return "NL2SMT_PROMPT_PLAN";
    if (key == "prompt_emit") return "NL2SMT_PROMPT_EMIT";
    if (key == "prompt_repair") return "NL2SMT_PROMPT_REPAIR";
    return nullptr;  /* use key as env name (e.g. NL2SMT_LLM_SCRIPT) */
}

void applyNl2smtEnv(const std::map<std::string, std::string>& nl2smt_opts) {
    for (const auto& kv : nl2smt_opts) {
        if (kv.first.empty()) continue;
        /* api_key: env overrides config (do not overwrite if already set) */
        if (kv.first == "api_key" || kv.first == "OPENAI_API_KEY") {
            const char* ek = getenv("NL2SMT_API_KEY");
            if (ek && ek[0] != '\0') continue;
            ek = getenv("OPENAI_API_KEY");
            if (ek && ek[0] != '\0') continue;
        }
        const char* envKey = nl2smtKeyToEnv(kv.first);
        if (!envKey) envKey = kv.first.c_str();
#ifdef _WIN32
        _putenv_s(envKey, kv.second.c_str());
#else
        setenv(envKey, kv.second.c_str(), 1);
#endif
    }
}

}  // namespace App
}  // namespace SMTParser
