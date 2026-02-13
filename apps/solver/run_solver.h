/* -*- Header -*-
 * Solver mode: run an external SMT solver on an SMT file.
 */
#ifndef APPS_SOLVER_RUN_SOLVER_HEADER
#define APPS_SOLVER_RUN_SOLVER_HEADER

#include <string>

namespace SMTParser {
namespace App {

/** Invoke solver at solverPath on smtFilePath. Returns solver exit code, or <0 on internal error. */
int runSolver(const std::string& solverPath, const std::string& smtFilePath);

void printSolverUsage(const char* prog);

}  // namespace App
}  // namespace SMTParser

#endif
