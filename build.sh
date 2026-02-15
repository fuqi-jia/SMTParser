#!/usr/bin/env bash
# Configure and build SMTParser. Checks dependencies and prints install hints if missing.
# Usage: ./build.sh [options]
#   --nl2smt    enable BUILD_NL2SMT (default: OFF)
#   --tests     enable BUILD_TESTS
#   --debug     enable ENABLE_DEBUG_SYMBOLS
#   <other>     passed to cmake (e.g. -DCMAKE_BUILD_TYPE=Debug)

set -e
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"
BUILD_DIR="${BUILD_DIR:-$REPO_ROOT/build}"
CMAKE_EXTRA=()
BUILD_NL2SMT=OFF
BUILD_TESTS=OFF
ENABLE_DEBUG=OFF

while [[ $# -gt 0 ]]; do
  case "$1" in
    --nl2smt)   BUILD_NL2SMT=ON ; shift ;;
    --tests)    BUILD_TESTS=ON  ; shift ;;
    --debug)    ENABLE_DEBUG=ON ; shift ;;
    *)          CMAKE_EXTRA+=("$1") ; shift ;;
  esac
done

# --- Check required tools and libs ---
MISSING=()
command -v cmake >/dev/null 2>&1 || MISSING+=(cmake)
command -v g++   >/dev/null 2>&1 || command -v c++ >/dev/null 2>&1 || MISSING+=(g++)
command -v pkg-config >/dev/null 2>&1 || MISSING+=(pkg-config)

if [[ ${#MISSING[@]} -gt 0 ]]; then
  echo "Missing required tools: ${MISSING[*]}"
  echo "Install with:"
  echo "  Ubuntu/Debian: sudo apt install -y build-essential cmake pkg-config"
  echo "  Fedora:        sudo dnf install -y gcc-c++ cmake pkg-config"
  echo "  macOS:         brew install cmake pkg-config"
  exit 1
fi

if ! pkg-config --exists gmp 2>/dev/null; then
  echo "GMP not found. Install development package:"
  echo "  Ubuntu/Debian: sudo apt install -y libgmp-dev"
  echo "  Fedora:        sudo dnf install -y gmp-devel"
  echo "  macOS:         brew install gmp"
  exit 1
fi

if ! pkg-config --exists mpfr 2>/dev/null; then
  echo "MPFR not found. Install development package:"
  echo "  Ubuntu/Debian: sudo apt install -y libmpfr-dev"
  echo "  Fedora:        sudo dnf install -y mpfr-devel"
  echo "  macOS:         brew install mpfr"
  exit 1
fi

# --- Configure and build ---
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
cmake "$REPO_ROOT" \
  -DBUILD_NL2SMT="$BUILD_NL2SMT" \
  -DBUILD_TESTS="$BUILD_TESTS" \
  -DENABLE_DEBUG_SYMBOLS="$ENABLE_DEBUG" \
  "${CMAKE_EXTRA[@]}"
make -j"$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)"

echo ""
echo "Build done. Executable: $BUILD_DIR/smtparser"
if [[ "$BUILD_NL2SMT" == ON ]]; then
  echo "NL2SMT is enabled. For natural-language tests, start the LLM first: ./llm.sh"
fi
