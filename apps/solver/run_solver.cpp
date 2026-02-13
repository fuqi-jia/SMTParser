/* -*- Source -*-
 * Solver mode: invoke external solver on SMT file.
 */
#include "solver/run_solver.h"
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <string>

#if !defined(_WIN32) && !defined(_WIN64)
#include <unistd.h>
#include <sys/wait.h>
#endif

namespace SMTParser {
namespace App {

void printSolverUsage(const char* prog) {
    std::cerr << "Usage: " << prog << " solve --solver <path> [file.smt2]\n"
              << "       " << prog << " solve --solver <path> --nl \"<natural language>\"\n"
              << "  Run the given SMT solver on the file (or on SMT generated from --nl).\n";
}

static int executeSolver(const std::string& solverPath, const std::string& smtFilePath) {
#ifdef _WIN32
    std::string cmd = "\"" + solverPath + "\" \"" + smtFilePath + "\"";
    return std::system(cmd.c_str());
#else
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        execl(solverPath.c_str(), solverPath.c_str(), smtFilePath.c_str(), static_cast<char*>(nullptr));
        _exit(127);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    return -1;
#endif
}

int runSolver(const std::string& solverPath, const std::string& smtFilePath) {
    if (solverPath.empty()) {
        std::cerr << "Error: --solver <path> is required.\n";
        return -1;
    }
    if (smtFilePath.empty()) {
        std::cerr << "Error: provide file.smt2 or use --nl (in main) to generate SMT first.\n";
        return -1;
    }
    return executeSolver(solverPath, smtFilePath);
}

}  // namespace App
}  // namespace SMTParser
