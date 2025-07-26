#!/bin/bash

# Script to run SMT parser on instances and delete successful ones
# Usage: ./run_and_del.sh [folder_path] [options]
# Options:
#   -v, --verbose     Show detailed error information
#   -d, --detailed    Show detailed results table
#   -f, --force       Force recompilation
#   -n, --dry-run     Show what would be deleted without actually deleting
#   -h, --help        Show help message

# Function to show help
show_help() {
    echo "Usage: $0 [folder_path] [options]"
    echo ""
    echo "Arguments:"
    echo "  folder_path        Directory containing .smt2 files to test and delete"
    echo ""
    echo "Options:"
    echo "  -v, --verbose     Show detailed error information"
    echo "  -d, --detailed    Show detailed results table"
    echo "  -f, --force       Force recompilation"
    echo "  -n, --dry-run     Show what would be deleted without actually deleting"
    echo "  -h, --help        Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 test/instances/schanda/spark     # Test and delete successful files in folder"
    echo "  $0 -n test/instances/schanda/spark  # Dry run - show what would be deleted"
    echo "  $0 -v test/instances/schanda/spark  # Verbose mode with detailed errors"
    echo "  $0 -d test/instances/schanda/spark  # Show detailed results table"
}

# Parse command line arguments
FORCE_COMPILE=false
VERBOSE=false
DETAILED=false
DRY_RUN=false
FOLDER_PATH=""

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
        -n|--dry-run)
            DRY_RUN=true
            shift
            ;;
        -*)
            echo "Unknown option: $1"
            show_help
            exit 1
            ;;
        *)
            if [[ -z "$FOLDER_PATH" ]]; then
                FOLDER_PATH="$1"
            else
                echo "Too many arguments. Only one folder path is allowed."
                show_help
                exit 1
            fi
            shift
            ;;
    esac
done

# Check if folder path is provided
if [[ -z "$FOLDER_PATH" ]]; then
    echo "Error: Folder path is required."
    show_help
    exit 1
fi

# Check if folder exists
if [[ ! -d "$FOLDER_PATH" ]]; then
    echo "Error: Folder '$FOLDER_PATH' does not exist."
    exit 1
fi

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
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
        cmake .. -DBUILD_TESTS=ON -DENABLE_TIMING=ON || {
            echo -e "${RED}Error: CMake configuration failed.${NC}"
            exit 1
        }
    else
        # Check if BUILD_TESTS is enabled in the existing configuration
        if ! grep -q "BUILD_TESTS:BOOL=ON" CMakeCache.txt 2>/dev/null; then
            echo -e "${YELLOW}Reconfiguring CMake with tests enabled...${NC}"
            cmake .. -DBUILD_TESTS=ON -DENABLE_TIMING=ON || {
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

# Default executable path (relative to project root)
DEFAULT_EXECUTABLE="$PROJECT_ROOT/build/test/test_smtparser_exe"
EXECUTABLE="$DEFAULT_EXECUTABLE"

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
fi

# Compile if needed
if [[ "$need_compile" == true ]]; then
    compile_executable
fi

# Final check if executable exists
if [[ ! -f "$EXECUTABLE" ]]; then
    echo -e "${RED}Error: Executable '$EXECUTABLE' still not found after compilation.${NC}"
    exit 1
fi

# Make executable if it's not already
chmod +x "$EXECUTABLE"

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}SMT Parser Test and Delete Runner${NC}"
echo -e "${BLUE}========================================${NC}"
if [[ "$VERBOSE" == true ]]; then
    echo "Project root: $PROJECT_ROOT"
fi
echo "Executable: $EXECUTABLE"
echo "Target folder: $FOLDER_PATH"
if [[ "$DRY_RUN" == true ]]; then
    echo -e "${CYAN}DRY RUN MODE - No files will be deleted${NC}"
fi
echo ""

# Initialize counters
total_files=0
success_count=0
failure_count=0
deleted_count=0
total_time=0

# Arrays to store detailed results
declare -a file_results
declare -a file_times
declare -a file_paths

# Create temporary files to store results
temp_results=$(mktemp)
temp_stats=$(mktemp)

# Process each file in the target directory (recursively)
while IFS= read -r file; do
    # Skip if file is empty
    if [[ ! -s "$file" ]]; then
        echo -e "${YELLOW}Skipping empty file: $file${NC}"
        continue
    fi
    
    total_files=$((total_files + 1))
    filename=$(basename "$file")
    
    echo -n "Processing $file... "
    
    # Run the executable and capture output (stdout+stderr)
    output=$("$EXECUTABLE" "$file" 2>&1)
    exit_code=$?
    
    # Parse the output
    if [[ $exit_code -eq 0 && $output == *"PARSE_SUCCESS"* ]]; then
        echo -e "${GREEN}SUCCESS${NC}"
        success_count=$((success_count + 1))
        
        # Extract statistics
        time_ms=$(echo "$output" | grep "TIME:" | cut -d':' -f2)
        total_time=$((total_time + time_ms))
        
        # Store results
        file_results[total_files]="SUCCESS"
        file_times[total_files]="$time_ms"
        file_paths[total_files]="$file"
        
        echo "    Time: ${time_ms}ms"
        
        # Delete the file if not in dry-run mode
        if [[ "$DRY_RUN" == true ]]; then
            echo -e "${CYAN}    [DRY RUN] Would delete: $file${NC}"
        else
            if rm "$file"; then
                echo -e "${GREEN}    Deleted: $file${NC}"
                deleted_count=$((deleted_count + 1))
            else
                echo -e "${RED}    Failed to delete: $file${NC}"
            fi
        fi
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
        file_paths[total_files]="$file"
        
        # Show error details if verbose mode
        if [[ "$VERBOSE" == true ]]; then
            echo "    Error details:"
            echo "$output" | sed 's/^/        /'
        fi
    fi
    
    # Write current stats to temp file
    echo "$total_files $success_count $failure_count $deleted_count $total_time" > "$temp_stats"
    
done < <(find "$FOLDER_PATH" -type f -name "*.smt2")

# Read final stats from temp file
if [[ -f "$temp_stats" ]]; then
    read -r total_files success_count failure_count deleted_count total_time < "$temp_stats"
    rm -f "$temp_stats"
fi

# Print summary
echo ""
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}SUMMARY${NC}"
echo -e "${BLUE}========================================${NC}"

if [[ $total_files -eq 0 ]]; then
    echo -e "${YELLOW}No .smt2 files found in directory.${NC}"
    rm -f "$temp_results"
    exit 0
fi

echo "Total files processed: $total_files"
echo -e "Successful parses: ${GREEN}$success_count${NC}"
echo -e "Failed parses: ${RED}$failure_count${NC}"

if [[ "$DRY_RUN" == true ]]; then
    echo -e "Files that would be deleted: ${CYAN}$success_count${NC}"
else
    echo -e "Files actually deleted: ${GREEN}$deleted_count${NC}"
fi

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

# Detailed results table (if requested)
if [[ "$DETAILED" == true ]]; then
    echo ""
    echo -e "${BLUE}Detailed Results:${NC}"
    echo "----------------------------------------"
    printf "%-30s %-10s %-10s %-10s\n" "File" "Result" "Time(ms)" "Action"
    echo "----------------------------------------"
    
    file_count=0
    find "$FOLDER_PATH" -type f -name "*.smt2" | while read -r file; do
        if [[ -s "$file" ]]; then
            file_count=$((file_count + 1))
            filename=$(basename "$file")
            
            if [[ ${#filename} -gt 28 ]]; then
                filename="${filename:0:25}..."
            fi
            
            result=${file_results[file_count]}
            time_val=${file_times[file_count]}
            
            # Determine action
            if [[ $result == "SUCCESS" ]]; then
                if [[ "$DRY_RUN" == true ]]; then
                    action="${CYAN}Would Delete${NC}"
                else
                    action="${GREEN}Deleted${NC}"
                fi
                result_colored="${GREEN}$result${NC}"
            else
                action="${YELLOW}Kept${NC}"
                result_colored="${RED}$result${NC}"
            fi
            
            printf "%-30s %-20s %-10s %-20s\n" "$filename" "$result_colored" "$time_val" "$action"
        fi
    done
    echo "----------------------------------------"
fi

# Show remaining files count
remaining_files=$(find "$FOLDER_PATH" -type f -name "*.smt2" | wc -l)
echo ""
echo -e "${BLUE}Remaining .smt2 files in directory: ${YELLOW}$remaining_files${NC}"

# Clean up temporary files
rm -f "$temp_results"

# Exit with appropriate code
if [[ $failure_count -gt 0 ]]; then
    exit 1
else
    exit 0
fi
