# SMTParser

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A C++ library for parsing, manipulating, and processing SMT-LIB (Satisfiability Modulo Theories Library) and OMT (Optimization Modulo Theories) formulas. The library implements an efficient graph representation for formulas, enabling comprehensive support for various SMT theories and optimization problems.

## Key Features

- **Comprehensive SMT-LIB2 Standard Support** - Fully compliant with the latest SMT-LIB2 specification
- **Multi-Theory Integration** - Seamless support for:
  - Core theory (Boolean operations)
  - Arithmetic theories (Integer, Real)
  - Bitvector theory with full operation support
  - IEEE-754 compliant Floating Point theory
  - String theory with Regular Expression operations
  - Theory of Arrays
- **DAG-Based Formula Representation** - Efficient memory usage and manipulation through shared subexpressions
- **Programmatic Expression Builder** - Comprehensive API for constructing and transforming expressions
- **Optimization Modulo Theories (OMT)** - Extended functionality for handling optimization objectives
- **Smart Pointer Integration** - All major components use std::shared_ptr for safe memory management

## System Requirements

- C++17 compatible compiler
- CMake 3.10+
- Boost library (system components)
- GMP (GNU Multiple Precision Arithmetic Library)
- MPFR (GNU Multiple Precision Floating-Point Reliable Library)

### Installing Dependencies

#### Ubuntu/Debian
```bash
sudo apt update
sudo apt install -y \
  build-essential \
  g++ \
  cmake \
  libboost-system-dev \
  libboost-filesystem-dev \
  libgmp-dev \
  libmpfr-dev
```

#### Fedora/RHEL/CentOS
```bash
# Fedora
sudo dnf install -y \
  gcc-c++ \
  cmake \
  boost-devel \
  gmp-devel \
  mpfr-devel

# RHEL/CentOS
sudo yum install -y \
  gcc-c++ \
  cmake \
  boost-devel \
  gmp-devel \
  mpfr-devel
```

#### macOS
Using [Homebrew](https://brew.sh/):
```bash
brew install \
  cmake \
  boost \
  gmp \
  mpfr
```

#### Windows

##### Using MSYS2
1. Install [MSYS2](https://www.msys2.org/)
2. Open MSYS2 MinGW 64-bit terminal and run:
```bash
pacman -Syu
pacman -S \
  mingw-w64-x86_64-gcc \
  mingw-w64-x86_64-cmake \
  mingw-w64-x86_64-boost \
  mingw-w64-x86_64-gmp \
  mingw-w64-x86_64-mpfr
```

##### Using vcpkg
1. Install [vcpkg](https://github.com/microsoft/vcpkg)
2. Install dependencies:
```bash
vcpkg install boost:x64-windows gmp:x64-windows mpfr:x64-windows
```

##### Using WSL (Windows Subsystem for Linux)
1. Install and set up [WSL](https://learn.microsoft.com/en-us/windows/wsl/install)
2. Follow the Ubuntu/Debian instructions to install dependencies within WSL

## Installation

### Standard CMake Build Process

```bash
# Clone the repository
git clone https://github.com/fuqi-jia/SMTParser.git
cd SMTParser

# Create and enter build directory
mkdir build && cd build

# Configure the build
cmake ..

# Compile the library (utilizing all available cores)
make -j$(nproc)

# Install the library (may require administrative privileges)
sudo make install
```

### Integration as Git Submodule

For projects using Git, SMTParser can be included as a submodule:

```bash
# Add the repository as a submodule
git submodule add https://github.com/fuqi-jia/SMTParser.git SMTParser

# Initialize the submodule
git submodule update --init --recursive

# Update the submodule to the latest version when needed
git submodule update --remote --merge
```

### Build TEST

To build and run the tests:

```bash
# Create and enter build directory
mkdir -p build && cd build

# Configure with tests enabled
cmake .. -DBUILD_TESTS=ON

# Build the project and tests
make -j$(nproc)

# Run all tests
cd test
for test in test_*; do ./$test; done

# Alternatively, run individual tests
./test_parser
./test_string_handling
```

You can also use the provided test script from the project root:

```bash
./test/run_tests.sh
```

### Build Configuration Options

| Option | Description | Default |
|--------|-------------|---------|
| `BUILD_SHARED_LIBS` | Build shared libraries (.so/.dll) | OFF |
| `BUILD_BOTH_LIBS` | Build both static (.a/.lib) and shared libraries | ON |
| `BUILD_TESTS` | Build test executables | OFF |

To customize the build configuration:

```bash
cmake -DBUILD_SHARED_LIBS=ON -DBUILD_BOTH_LIBS=OFF ..
```

## Usage Examples

### Parsing SMT-LIB2 Files

```cpp
#include "parser.h"
#include <iostream>

int main() {
    // Initialize the parser
    SMTParser::Parser parser;

    // Parse an SMT-LIB2 file
    if (!parser.parse("formula.smt2")) {
        std::cerr << "Error parsing file" << std::endl;
        return 1;
    }

    // Retrieve the parsed assertions
    auto assertions = parser.getAssertions();

    // Output the assertions
    for(auto constraint: assertions){
        std::cout << parser->toString(constraint) << std::endl;
    }

    return 0;
}
```

### Using Smart Pointers and Factory Methods

```cpp
#include "parser.h"
#include <iostream>

int main() {
    // Create a parser using factory method
    auto parser = SMTParser::newParser();
    
    // Alternative: create a parser with file in one step
    auto fileParser = SMTParser::newParser("formula.smt2");
    
    // Create a model
    auto model = SMTParser::newModel();
    
    // Create and manipulate variables
    auto x = parser->mkVarInt("x");
    auto y = parser->mkVarInt("y");
    
    // Add assignments to model
    model->add(x, parser->mkConstInt(10));
    model->add(y, parser->mkConstInt(20));
    
    // Evaluate expressions using the model
    auto expr = parser->mkAdd({x, y});
    auto result = parser->evaluate(expr, model);
    
    std::cout << "x + y = " << parser->toString(result) << std::endl;
    
    return 0;
}
```

### Constructing Expressions Programmatically

```cpp
#include "parser.h"
#include <iostream>

int main() {
    // Initialize the parser engine
    SMTParser::Parser parser;

    // Create integer variables
    auto x = parser.mkVar(INT_SORT, "x");
    auto y = parser.mkVarInt("y");

    // Construct the expression: (x + y) > 10
    auto sum = parser.mkAdd({x, y});
    auto constant = parser.mkConstInt(10);
    auto constraint = parser.mkGt(sum, constant);

    // Output SMT-LIB2 representation
    std::cout << parser->toString(constraint) << std::endl;
    // Output: (> (+ x y) 10)

    return 0;
}
```

### Compiling Client Applications

When building applications that use SMTParser, link against the library and its dependencies:

```bash
g++ -std=c++17 -o application main.cpp -lsmtparser -lgmp
```

### Complete Project Example

For a complete project example, check out [SMTParser-Test](https://github.com/fuqi-jia/SMTParser-Test) which demonstrates how to integrate and use the library as a Git submodule.

#### Project Structure:
```
SMTParser-Test/
├── CMakeLists.txt          # Build configuration
├── SMTParser/           # Submodule
├── src/                    # Application source code
│   └── main.cpp
└── test/                   # Test SMT-LIB2 files
    └── 1.smt2
```

#### Setting Up the Project:

1. Clone the repository and initialize the submodule:
```bash
git clone https://github.com/fuqi-jia/SMTParser-Test.git
cd SMTParser-Test
git submodule update --init --recursive
```

2. Build the project:
```bash
mkdir build && cd build
cmake ..
make -j$(nproc)
```

3. Run the test application:
```bash
./SMTParser_Test ../test/1.smt2
```

This simple example demonstrates how to parse and process an SMT-LIB2 file. You can use this project as a template for your own applications.

## API Reference

### Core Components and Smart Pointer Types

| Component | Smart Pointer Type | Description |
|-----------|-------------------|-------------|
| `Parser` | `ParserPtr` | Main class for parsing SMT-LIB2 files and managing expressions |
| `DAGNode` | `NodePtr` | Represents expressions as nodes in a "directed acyclic graph" |
| `Sort` | `SortPtr` | Encapsulates SMT-LIB2 type system |
| `Objective` | `ObjectivePtr` | Represents optimization objectives for OMT problems |
| `SingleObjective` | `SingleObjectivePtr` | Represents a single optimization objective |
| `MetaObjective` | `MetaObjectivePtr` | Represents a meta-optimization objective |
| `Model` | `ModelPtr` | Represents a model with variable assignments |

### Factory Methods

| Method | Description |
|--------|-------------|
| `newParser()` | Creates a new parser instance |
| `newParser(const std::string& filename)` | Creates a new parser and parses the specified file |
| `newModel()` | Creates a new model instance |

### Primary API Functions

| Category | Function Examples |
|----------|------------------|
| Variable Creation | `mkVar`, `mkVarInt`, `mkVarReal`, `mkVarBool`, `...` |
| Constant Creation | `mkConstInt`, `mkConstReal`, `mkTrue`, `mkFalse`, `...` |
| Expression Building | `mkOper`, `mkEq`, `mkDistinct`, `mkNot`, `mkAnd`, `mkOr`, `...` |
| Arithmetic Operations | `mkAdd`, `mkSub`, `mkMul`, `mkDiv`, `mkPow`, `...` |
| Comparison Operations | `mkLt`, `mkLe`, `mkGt`, `mkGe`, `...` |
| Bitvector Operations | `mkBvAnd`, `mkBvOr`, `mkBvXor`, `mkBvAdd`, `mkBvShl`, `...` |
| String Operations | `mkStrLen`, `mkStrConcat`, `mkStrSubstr`, `mkStrIndexof`, `...` |
| Regular Expression Operations | `mkStrToReg`, `mkRegUnion`, `mkRegStar`, `...` |
| Array Operations | `mkSelect`, `mkStore` |
| Floating Point Operations | `mkFpAdd`, `mkFpMul`, `mkFpDiv`, `mkFpEq`, `...` |
| Model Operations | `add`, `get`, `...` |

## API Documentation

You can generate detailed API documentation using Doxygen:

### Installing Doxygen

#### Ubuntu/Debian
```bash
sudo apt-get install doxygen
```

#### CentOS/RHEL
```bash
sudo yum install doxygen
```

#### macOS
```bash
brew install doxygen
```

### Generating Documentation

To generate the documentation, run:

```bash
cd path/to/SMTParser
doxygen Doxyfile
```

### Viewing Documentation

After generating the documentation, you can view it in your browser:

```bash
# Linux
xdg-open docs/html/index.html

# macOS
open docs/html/index.html

# Windows
start docs/html/index.html
```

Or simply navigate to `SMTParser/docs/html/index.html` in your file browser and open it with any web browser.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Development Status

**Active Development** - This project is under continuous improvement and development. New features and optimizations are being added regularly.

## Contact

For technical inquiries or support, please contact:

**Fuqi Jia**  
Email: jiafq@ios.ac.cn  
Institute of Software, Chinese Academy of Sciences

