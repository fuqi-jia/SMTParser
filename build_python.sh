#!/bin/bash

# Build script for SMTParser Python bindings
# This script builds the Python extension module using setuptools

set -e  # Exit on any error

echo "========================================"
echo "SMTParser Python Bindings Build Script"
echo "========================================"

# Check if Python is available
if ! command -v python3 &> /dev/null; then
    echo "Error: python3 is not installed or not in PATH"
    exit 1
fi

echo "Using Python: $(which python3)"
echo "Python version: $(python3 --version)"

# Check if pip is available
if ! command -v pip3 &> /dev/null; then
    echo "Error: pip3 is not installed or not in PATH"
    exit 1
fi

# Install required Python packages
echo "Installing required Python packages..."
pip3 install --user pybind11 setuptools wheel

# Check for required system libraries
echo "Checking for required system libraries..."

# Function to check if a library exists
check_library() {
    local lib_name=$1
    local header_file=$2
    
    echo -n "Checking for $lib_name... "
    
    # Check for header file
    if find /usr/include /usr/local/include /opt/local/include /mingw64/include -name "$header_file" 2>/dev/null | head -1 | grep -q "$header_file"; then
        echo "found"
    else
        echo "NOT FOUND"
        echo "Warning: $lib_name development headers not found."
        echo "Please install the development package:"
        echo "  Ubuntu/Debian: sudo apt install lib${lib_name,,}-dev"
        echo "  Fedora/RHEL: sudo dnf install $lib_name-devel"
        echo "  macOS: brew install $lib_name"
        echo ""
    fi
}

check_library "GMP" "gmp.h"
check_library "MPFR" "mpfr.h"

# Create python_binding directory if it doesn't exist
if [ ! -d "python_binding" ]; then
    echo "Error: python_binding directory not found"
    echo "Please make sure you are running this script from the SMTParser root directory"
    exit 1
fi

# Build the extension
echo "Building Python extension..."
echo "----------------------------------------"

# Clean previous builds
if [ -d "build" ]; then
    echo "Cleaning previous builds..."
    rm -rf build/
fi

if [ -d "dist" ]; then
    rm -rf dist/
fi

# Remove any existing .so files
find . -name "*.so" -delete 2>/dev/null || true

# Build the extension
echo "Running setup.py build_ext..."
python3 setup.py build_ext --inplace

# Check if build was successful
if [ $? -eq 0 ]; then
    echo "Build completed successfully!"
    
    # Check if the .so file was created
    if ls smtparser*.so 1> /dev/null 2>&1; then
        echo "Extension module created: $(ls smtparser*.so)"
        
        # Test the module
        echo "Testing the module..."
        python3 -c "import smtparser; print('SMTParser module imported successfully!')"
        
        if [ $? -eq 0 ]; then
            echo ""
            echo "========================================="
            echo "BUILD SUCCESSFUL!"
            echo "========================================="
            echo ""
            echo "You can now use the SMTParser Python module:"
            echo "  python3 -c 'import smtparser'"
            echo ""
            echo "To run the example:"
            echo "  python3 python_binding/example.py"
            echo ""
            echo "To install system-wide:"
            echo "  python3 setup.py install"
            echo "  # or"
            echo "  pip3 install ."
            echo ""
        else
            echo "Warning: Module built but import test failed"
        fi
    else
        echo "Error: Extension module (.so file) was not created"
        exit 1
    fi
else
    echo "Build failed!"
    exit 1
fi 