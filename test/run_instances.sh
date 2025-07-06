#!/bin/bash

# Script to run SMT parser on all instances and collect statistics
# Usage: ./run_instances.sh [executable_path] [options]
# Options:
#   -v, --verbose     Show detailed error information
#   -d, --detailed    Show detailed results table
#   -f, --force       Force recompilation
#   -h, --help        Show help message

# Function to show help
show_help() {
    echo "Usage: $0 [executable_path] [options]"
    echo ""
    echo "Options:"
    echo "  -v, --verbose     Show detailed error information"
    echo "  -d, --detailed    Show detailed results table"
    echo "  -f, --force       Force recompilation"
    echo "  -h, --help        Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0                                    # Use default executable, compile if needed"
    echo "  $0 -f                                 # Force recompile and run"
    echo "  $0 /path/to/executable                # Use custom executable"
    echo "  $0 -d                                 # Show detailed results"
    echo "  $0 -v                                 # Show verbose errors"
    echo "  $0 -fdv                               # Force recompile with detailed and verbose output"
}

# Parse command line arguments
FORCE_COMPILE=false
VERBOSE=false
DETAILED=false
CUSTOM_EXECUTABLE=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -f|--force)
            FORCE_COMPILE=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -d|--detailed)
            DETAILED=true
            shift
            ;;
        -*)
            echo "Unknown option: $1"
            show_help
            exit 1
            ;;
        *)
            if [[ -z "$CUSTOM_EXECUTABLE" ]]; then
                CUSTOM_EXECUTABLE="$1"
            else
                echo "Too many arguments. Only one executable path is allowed."
                show_help
                exit 1
            fi
            shift
            ;;
    esac
done

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to find project root directory
find_project_root() {
    local current_dir=$(pwd)
    local search_dir="$current_dir"
    
    # Look for CMakeLists.txt in current directory and parent directories
    while [[ "$search_dir" != "/" ]]; do
        if [[ -f "$search_dir/CMakeLists.txt" && -d "$search_dir/include" && -d "$search_dir/src" ]]; then
            echo "$search_dir"
            return 0
        fi
        search_dir=$(dirname "$search_dir")
    done
    
    # If not found, try current directory
    if [[ -f "CMakeLists.txt" ]]; then
        echo "$current_dir"
        return 0
    fi
    
    return 1
}

# Function to compile the executable
compile_executable() {
    echo -e "${YELLOW}Compiling executable...${NC}"
    
    # Find project root
    local project_root
    project_root=$(find_project_root)
    if [[ $? -ne 0 ]]; then
        echo -e "${RED}Error: Could not find project root directory.${NC}"
        echo "Please run this script from within the SMTLIBParser project directory."
        exit 1
    fi
    
    if [[ "$VERBOSE" == true ]]; then
        echo -e "${BLUE}Project root: $project_root${NC}"
    fi
    
    # Change to project root
    cd "$project_root"
    
    # Check if build directory exists
    if [[ ! -d "build" ]]; then
        echo -e "${YELLOW}Creating build directory...${NC}"
        mkdir -p build
    fi
    
    # Change to build directory and compile
    cd build
    
    # Check if CMakeCache.txt exists and if tests are enabled
    if [[ ! -f "CMakeCache.txt" ]]; then
        echo -e "${YELLOW}Running CMake configuration...${NC}"
        cmake .. -DBUILD_TESTS=ON || {
            echo -e "${RED}Error: CMake configuration failed.${NC}"
            exit 1
        }
    else
        # Check if BUILD_TESTS is enabled in the existing configuration
        if ! grep -q "BUILD_TESTS:BOOL=ON" CMakeCache.txt 2>/dev/null; then
            echo -e "${YELLOW}Reconfiguring CMake with tests enabled...${NC}"
            cmake .. -DBUILD_TESTS=ON || {
                echo -e "${RED}Error: CMake reconfiguration failed.${NC}"
                exit 1
            }
        fi
    fi
    
    # Build the entire project with tests enabled
    echo -e "${YELLOW}Building SMTParser project with tests...${NC}"
    
    # Build everything (this will build the library and all tests)
    make || {
        echo -e "${RED}Error: Build failed.${NC}"
        echo -e "${YELLOW}Trying to build specific targets...${NC}"
        
        # Try to build just what we need
        if make smtparser_static 2>/dev/null && make test_smtparser_exe 2>/dev/null; then
            echo -e "${GREEN}Successfully built required targets.${NC}"
        else
            echo -e "${RED}Failed to build required targets.${NC}"
            echo -e "${YELLOW}Available targets:${NC}"
            make help | grep -E "(smtparser|test_)" || echo "No matching targets found"
            exit 1
        fi
    }
    
    echo -e "${GREEN}Compilation successful!${NC}"
}

# Initialize paths after function definitions
# Find project root for path resolution
PROJECT_ROOT=$(find_project_root 2>/dev/null)
if [[ -z "$PROJECT_ROOT" ]]; then
    echo -e "${RED}Error: Could not find project root directory.${NC}"
    echo "Please run this script from within the SMTLIBParser project directory."
    echo "Current directory: $(pwd)"
    exit 1
fi

# Show a brief message about where we're operating
current_dir=$(basename "$(pwd)")
if [[ "$current_dir" == "test" ]]; then
    echo -e "${BLUE}Running from test directory, using project root: $(basename "$PROJECT_ROOT")${NC}"
fi

# Default executable path (relative to project root)
DEFAULT_EXECUTABLE="$PROJECT_ROOT/build/test/test_smtparser_exe"
EXECUTABLE="${CUSTOM_EXECUTABLE:-$DEFAULT_EXECUTABLE}"

# Instances directory (relative to project root)
INSTANCES_DIR="$PROJECT_ROOT/test/instances"

# Source files to check for changes (relative to project root)
SOURCE_FILE="$PROJECT_ROOT/test/test_smtparser_exe.cpp"
INCLUDE_DIR="$PROJECT_ROOT/include"

# Check if we need to compile
need_compile=false

# Force compilation if requested
if [[ "$FORCE_COMPILE" == true ]]; then
    echo -e "${YELLOW}Force compilation requested.${NC}"
    need_compile=true
fi

# Check if executable exists
if [[ ! -f "$EXECUTABLE" ]]; then
    echo -e "${YELLOW}Executable '$EXECUTABLE' not found.${NC}"
    need_compile=true
elif [[ "$EXECUTABLE" == "$DEFAULT_EXECUTABLE" && "$FORCE_COMPILE" == false ]]; then
    # Only check for source changes if using default executable and not forcing
    if [[ -f "$SOURCE_FILE" ]]; then
        # Check if source file is newer than executable
        if [[ "$SOURCE_FILE" -nt "$EXECUTABLE" ]]; then
            echo -e "${YELLOW}Source file is newer than executable.${NC}"
            need_compile=true
        fi
        
        # Check if any header files are newer than executable
        if [[ -d "$INCLUDE_DIR" ]]; then
            for header_file in "$INCLUDE_DIR"/*.h; do
                if [[ -f "$header_file" && "$header_file" -nt "$EXECUTABLE" ]]; then
                    echo -e "${YELLOW}Header file $header_file is newer than executable.${NC}"
                    need_compile=true
                    break
                fi
            done
        fi
    fi
fi

# Compile if needed
if [[ "$need_compile" == true ]]; then
    # Only compile if using default executable
    if [[ "$EXECUTABLE" == "$DEFAULT_EXECUTABLE" ]]; then
        compile_executable
    else
        echo -e "${RED}Cannot compile custom executable: $EXECUTABLE${NC}"
        echo "Please compile manually or use the default executable."
        exit 1
    fi
fi

# Final check if executable exists
if [[ ! -f "$EXECUTABLE" ]]; then
    echo -e "${RED}Error: Executable '$EXECUTABLE' still not found after compilation.${NC}"
    echo "Usage: $0 [executable_path]"
    echo "Default executable path: $DEFAULT_EXECUTABLE"
    exit 1
fi

# Check if instances directory exists
if [[ ! -d "$INSTANCES_DIR" ]]; then
    echo -e "${RED}Error: Instances directory '$INSTANCES_DIR' not found.${NC}"
    echo "Expected directory: $INSTANCES_DIR"
    exit 1
fi

# Make executable if it's not already
chmod +x "$EXECUTABLE"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}SMT Parser Instance Runner${NC}"
echo -e "${BLUE}========================================${NC}"
if [[ "$VERBOSE" == true ]]; then
    echo "Project root: $PROJECT_ROOT"
fi
echo "Executable: $EXECUTABLE"
echo "Instances directory: $INSTANCES_DIR"
echo ""

# Initialize counters
total_files=0
success_count=0
failure_count=0
total_time=0
total_assertions=0
total_variables=0
total_functions=0

# Arrays to store detailed results
declare -a file_results
declare -a file_times
declare -a file_stats

# Process each file in the instances directory
for file in "$INSTANCES_DIR"/*; do
    # Skip if not a regular file
    if [[ ! -f "$file" ]]; then
        continue
    fi
    
    # Skip if file is empty
    if [[ ! -s "$file" ]]; then
        echo -e "${YELLOW}Skipping empty file: $file${NC}"
        continue
    fi
    
    total_files=$((total_files + 1))
    filename=$(basename "$file")
    
    echo -n "Processing $filename... "
    
    # Run the executable and capture output
    output=$("$EXECUTABLE" "$file" 2>&1)
    exit_code=$?
    
    # Parse the output
    if [[ $exit_code -eq 0 && $output == *"PARSE_SUCCESS"* ]]; then
        echo -e "${GREEN}SUCCESS${NC}"
        success_count=$((success_count + 1))
        
        # Extract statistics
        assertions=$(echo "$output" | grep "ASSERTIONS:" | cut -d':' -f2)
        variables=$(echo "$output" | grep "VARIABLES:" | cut -d':' -f2)
        functions=$(echo "$output" | grep "FUNCTIONS:" | cut -d':' -f2)
        time_ms=$(echo "$output" | grep "TIME:" | cut -d':' -f2)
        
        # Add to totals
        total_assertions=$((total_assertions + assertions))
        total_variables=$((total_variables + variables))
        total_functions=$((total_functions + functions))
        total_time=$((total_time + time_ms))
        
        # Store results
        file_results[total_files]="SUCCESS"
        file_times[total_files]="$time_ms"
        file_stats[total_files]="A:$assertions V:$variables F:$functions"
        
        echo "    Time: ${time_ms}ms, Assertions: $assertions, Variables: $variables, Functions: $functions"
    else
        echo -e "${RED}FAILURE${NC}"
        failure_count=$((failure_count + 1))
        
        # Extract time if available
        time_ms=$(echo "$output" | grep "TIME:" | cut -d':' -f2)
        if [[ -n "$time_ms" ]]; then
            total_time=$((total_time + time_ms))
            file_times[total_files]="$time_ms"
            echo "    Time: ${time_ms}ms"
        else
            file_times[total_files]="N/A"
        fi
        
        file_results[total_files]="FAILURE"
        file_stats[total_files]="N/A"
        
        # Show error details if verbose mode
        if [[ "$VERBOSE" == true ]]; then
            echo "    Error details:"
            echo "$output" | sed 's/^/        /'
        fi
    fi
done

# Print summary
echo ""
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}SUMMARY${NC}"
echo -e "${BLUE}========================================${NC}"

if [[ $total_files -eq 0 ]]; then
    echo -e "${YELLOW}No files found in instances directory.${NC}"
    exit 0
fi

echo "Total files processed: $total_files"
echo -e "Successful parses: ${GREEN}$success_count${NC}"
echo -e "Failed parses: ${RED}$failure_count${NC}"

# Calculate success rate
if [[ $total_files -gt 0 ]]; then
    success_rate=$(echo "scale=2; $success_count * 100 / $total_files" | bc -l 2>/dev/null || echo "$(($success_count * 100 / $total_files))")
    echo "Success rate: ${success_rate}%"
fi

# Time statistics
if [[ $total_time -gt 0 ]]; then
    avg_time=$(echo "scale=2; $total_time / $total_files" | bc -l 2>/dev/null || echo "$(($total_time / $total_files))")
    echo "Total time: ${total_time}ms"
    echo "Average time: ${avg_time}ms"
fi

# Content statistics (only for successful parses)
if [[ $success_count -gt 0 ]]; then
    echo ""
    echo -e "${BLUE}Content Statistics (successful parses only):${NC}"
    echo "Total assertions: $total_assertions"
    echo "Total variables: $total_variables"
    echo "Total functions: $total_functions"
    
    avg_assertions=$(echo "scale=2; $total_assertions / $success_count" | bc -l 2>/dev/null || echo "$(($total_assertions / $success_count))")
    avg_variables=$(echo "scale=2; $total_variables / $success_count" | bc -l 2>/dev/null || echo "$(($total_variables / $success_count))")
    avg_functions=$(echo "scale=2; $total_functions / $success_count" | bc -l 2>/dev/null || echo "$(($total_functions / $success_count))")
    
    echo "Average assertions per file: $avg_assertions"
    echo "Average variables per file: $avg_variables"
    echo "Average functions per file: $avg_functions"
fi

# Detailed results table (if requested)
if [[ "$DETAILED" == true ]]; then
    echo ""
    echo -e "${BLUE}Detailed Results:${NC}"
    echo "----------------------------------------"
    printf "%-30s %-10s %-10s %-20s\n" "File" "Result" "Time(ms)" "Stats"
    echo "----------------------------------------"
    
    file_count=0
    for file in "$INSTANCES_DIR"/*; do
        if [[ -f "$file" && -s "$file" ]]; then
            file_count=$((file_count + 1))
            filename=$(basename "$file")
            
            if [[ ${#filename} -gt 28 ]]; then
                filename="${filename:0:25}..."
            fi
            
            result=${file_results[file_count]}
            time_val=${file_times[file_count]}
            stats=${file_stats[file_count]}
            
            # Color coding for result
            if [[ $result == "SUCCESS" ]]; then
                result_colored="${GREEN}$result${NC}"
            else
                result_colored="${RED}$result${NC}"
            fi
            
            printf "%-30s %-20s %-10s %-20s\n" "$filename" "$result_colored" "$time_val" "$stats"
        fi
    done
    echo "----------------------------------------"
fi

# Exit with appropriate code
if [[ $failure_count -gt 0 ]]; then
    exit 1
else
    exit 0
fi
