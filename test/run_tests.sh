#!/bin/bash

# Set up colored output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Change to project root directory
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

# Create build directory
mkdir -p build
cd build

# Configure with CMake
echo -e "${YELLOW}Configuring project...${NC}"
cmake .. -DBUILD_TESTS=ON
if [ $? -ne 0 ]; then
    echo -e "${RED}CMake configuration failed!${NC}"
    exit 1
fi

# Compile
echo -e "${YELLOW}Building project...${NC}"
make -j$(nproc)
if [ $? -ne 0 ]; then
    echo -e "${RED}Build failed!${NC}"
    exit 1
fi

# Run all tests
echo -e "${YELLOW}Running tests...${NC}"
cd test

# Find all test executables
TEST_EXES=$(find . -type f -executable -name "test_*" 2>/dev/null)

# If no executables found, try explicit names
if [ -z "$TEST_EXES" ]; then
    echo -e "${YELLOW}No test executables found automatically, trying explicit filenames...${NC}"
    
    # Check for specific test executables
    if [ -f "./test_parser" ]; then
        TEST_EXES="$TEST_EXES ./test_parser"
    fi
    
    if [ -f "./test_string_handling" ]; then
        TEST_EXES="$TEST_EXES ./test_string_handling"
    fi
    
    if [ -z "$TEST_EXES" ]; then
        echo -e "${RED}No test executables found!${NC}"
        exit 1
    fi
fi

# Run each test
FAILED_TESTS=0
for test in $TEST_EXES; do
    echo -e "${YELLOW}Running $test...${NC}"
    $test
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}$test passed!${NC}"
    else
        echo -e "${RED}$test failed!${NC}"
        FAILED_TESTS=$((FAILED_TESTS+1))
    fi
    echo ""
done

# Report test results
if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}$FAILED_TESTS tests failed!${NC}"
    exit 1
fi 