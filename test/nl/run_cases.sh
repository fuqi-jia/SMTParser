#!/usr/bin/env bash
# Run each test case in test/nl/inputs/*.nl with smtparser nl (run from build dir with LLM configured).
# Each case is run twice: Structured (LD+APT+build) and DirectTextual (single LLM -> SMT2).
# Requires: LLM endpoint running (e.g. LiteLLM proxy). If you see "HTTP request failed (connection/timeout)",
#           start the service or check endpoint/timeout in .config/llm.conf.
# Usage from repo root: ./test/nl/run_cases.sh [smtparser_exe]
# Usage from build:      ../test/nl/run_cases.sh [./smtparser]

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
INPUTS_DIR="${SCRIPT_DIR}/inputs"
EXE="${1:-./smtparser}"
# .config at repo root; resolve to absolute path so nl subcommand finds it from any cwd
CONFIG="${REPO_ROOT}/.config/llm.conf"

if [[ ! -d "$INPUTS_DIR" ]]; then
  echo "No inputs dir: $INPUTS_DIR"
  exit 1
fi

if [[ ! -f "$CONFIG" ]]; then
  echo "Config not found: $CONFIG (copy .config/llm.conf.example to .config/llm.conf and edit)"
  exit 1
fi

for f in "$INPUTS_DIR"/*.nl; do
  [[ -f "$f" ]] || continue
  name="$(basename "$f" .nl)"
  nl="$(cat "$f")"
  echo "===== $name ====="
  echo "--- Structured (default) ---"
  "$EXE" nl --config "$CONFIG" "$nl" || true
  echo ""
  echo "--- DirectTextual ---"
  "$EXE" nl --nl-strategy=DirectTextual --config "$CONFIG" "$nl" || true
  echo ""
done
