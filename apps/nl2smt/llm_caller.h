/* -*- Header -*-
 * NL2SMT LLM caller: run configured command (e.g. Python script) to call LLM, return SMT-LIB2 string.
 */
#ifndef NL2SMT_LLM_CALLER_HEADER
#define NL2SMT_LLM_CALLER_HEADER

#include <string>

namespace SMTParser {
namespace NL2SMT {

/**
 * Call LLM with the given natural language input (legacy single-shot: NL → SMT-LIB2).
 * Runs NL2SMT_LLM_SCRIPT (or NL2SMT_LLM_CMD) with input from a temp file; returns stdout as SMT-LIB2.
 * On failure returns empty string and error message can be retrieved via lastError().
 */
std::string callLLM(const std::string& naturalLanguageInput);

/** Tree-Plan phase: NL → JSON plan. Requires NL2SMT_LLM_SCRIPT. */
std::string callLLM_Plan(const std::string& naturalLanguageInput);

/** Emit phase: JSON plan → SMT-LIB2. Requires NL2SMT_LLM_SCRIPT. */
std::string callLLM_Emit(const std::string& planJson);

/** Repair phase: parser error + plan + previous SMT → fixed SMT-LIB2. Requires NL2SMT_LLM_SCRIPT. */
std::string callLLM_Repair(const std::string& errorMessage, const std::string& planJson, const std::string& previousSmt);

std::string llmCallerLastError();

}  // namespace NL2SMT
}  // namespace SMTParser

#endif
