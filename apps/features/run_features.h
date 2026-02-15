/* -*- Header -*-
 * Feature subcommand: parse SMT file and print syntax features (logic, assertions, variables, etc.).
 */
#ifndef APPS_FEATURES_RUN_FEATURES_HEADER
#define APPS_FEATURES_RUN_FEATURES_HEADER

namespace SMTParser {
namespace App {

/** Parse smtFilePath and print syntax features. Returns 0 on success, non-zero on error. */
int runFeatures(const char* smtFilePath);

}  // namespace App
}  // namespace SMTParser

#endif
