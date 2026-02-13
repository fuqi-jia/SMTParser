/* -*- Source -*-
 * NL2SMT LLM caller: invoke external command (e.g. python llm_call.py) and return stdout.
 */
#include "nl2smt/llm_caller.h"
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>
#include <string>

#if defined(_WIN32) || defined(_WIN64)
#include <io.h>
#define popen _popen
#define pclose _pclose
#else
#include <unistd.h>
#endif

namespace SMTParser {
namespace NL2SMT {

namespace {
std::string g_llm_last_error;
}

std::string llmCallerLastError() {
    return g_llm_last_error;
}

static std::string getScriptPath() {
    const char* script = std::getenv("NL2SMT_LLM_SCRIPT");
    if (script && script[0] != '\0')
        return script;
    const char* cmd = std::getenv("NL2SMT_LLM_CMD");
    if (cmd && cmd[0] != '\0')
        return "";  // full command, no script path
    g_llm_last_error = "Set NL2SMT_LLM_SCRIPT to the path to llm_call.py (e.g. /path/to/apps/nl2smt/llm_call.py), or NL2SMT_LLM_CMD for full command.";
    return "";
}

/** Strip ```smt2 or ``` from start/end of model output. */
static std::string stripMarkdownCodeBlock(std::string s) {
    while (!s.empty() && (s.back() == '\r' || s.back() == '\n'))
        s.pop_back();
    if (s.size() >= 3 && s.substr(0, 3) == "```") {
        size_t first = s.find('\n');
        if (first != std::string::npos)
            s = s.substr(first + 1);
        else
            s = s.substr(3);
    }
    if (s.size() >= 3 && s.substr(s.size() - 3) == "```")
        s = s.substr(0, s.size() - 3);
    while (!s.empty() && (s.back() == '\r' || s.back() == '\n'))
        s.pop_back();
    return s;
}

std::string callLLM(const std::string& naturalLanguageInput) {
    g_llm_last_error.clear();
    if (naturalLanguageInput.empty()) {
        g_llm_last_error = "Empty input.";
        return "";
    }

    std::string cmd;
    const char* fullCmd = std::getenv("NL2SMT_LLM_CMD");
    if (fullCmd && fullCmd[0] != '\0') {
        cmd = fullCmd;
    } else {
        std::string scriptPath = getScriptPath();
        if (scriptPath.empty())
            return "";
        cmd = "python \"" + scriptPath + "\"";
    }

    std::string inPath;
    std::string pidStr = std::to_string(static_cast<long>(getpid()));
    const char* tmpDir = std::getenv("TMPDIR");
    if (!tmpDir) tmpDir = std::getenv("TEMP");
    if (!tmpDir) tmpDir = "/tmp";
    inPath = std::string(tmpDir) + "/nl2smt_in_" + pidStr + ".txt";

    std::ofstream inFile(inPath);
    if (!inFile) {
        g_llm_last_error = "Cannot write temp input file: " + inPath;
        return "";
    }
    inFile << naturalLanguageInput;
    inFile.close();
    if (!inFile) {
        g_llm_last_error = "Failed to write temp file.";
        return "";
    }

    cmd += " \"" + inPath + "\"";

    FILE* fp = popen(cmd.c_str(), "r");
    if (!fp) {
        g_llm_last_error = "Failed to run LLM command. Check NL2SMT_LLM_SCRIPT or NL2SMT_LLM_CMD.";
        std::remove(inPath.c_str());
        return "";
    }

    std::ostringstream out;
    char buf[4096];
    while (fgets(buf, sizeof(buf), fp))
        out << buf;
    int status = pclose(fp);
    std::remove(inPath.c_str());

    if (status != 0) {
        g_llm_last_error = "LLM command exited with status " + std::to_string(status) + ". Check OPENAI_API_KEY and script path.";
        return "";
    }

    return stripMarkdownCodeBlock(out.str());
}

}  // namespace NL2SMT
}  // namespace SMTParser
