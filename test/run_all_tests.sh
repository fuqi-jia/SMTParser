#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="${SOMTPARSER_BUILD_DIR:-${PROJECT_ROOT}/build}"

# SOMTPARSER_BUILD_TOOLS defaults to OFF, and tools/CMakeLists.txt is where
# SOMTParser.test_somt_convert_cli_contract is registered -- so without this flag
# that test is not merely skipped, it does not exist, and ctest reports a clean
# run one test shorter. It went unnoticed because a build directory configured
# once with the flag keeps it in its cache: the test ran locally for anyone who
# had ever enabled tools, and never in CI.
#
# What it guards is somt-convert's stdout, stderr and exit codes, which the
# evaluation harness pipes straight into a solver. That contract is exactly the
# thing that must not drift silently.
cmake -S "${PROJECT_ROOT}" -B "${BUILD_DIR}" \
  -DCMAKE_BUILD_TYPE="${CMAKE_BUILD_TYPE:-Debug}" \
  -DSOMTPARSER_BUILD_TESTS=ON \
  -DSOMTPARSER_BUILD_TOOLS=ON
# Bare `--parallel` uses every core, which is right on a CI runner and wrong on a
# memory-constrained WSL2 box -- a full-core build of this tree took one down mid-run.
# SOMTPARSER_BUILD_JOBS caps both phases; unset reproduces the previous behaviour
# exactly, so CI is unaffected.
JOBS="${SOMTPARSER_BUILD_JOBS:-}"
cmake --build "${BUILD_DIR}" --parallel ${JOBS}
ctest --test-dir "${BUILD_DIR}" --output-on-failure ${JOBS:+-j ${JOBS}}
