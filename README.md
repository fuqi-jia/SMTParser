# SMTLIBParser

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A high-performance C++ library for parsing, manipulating, and processing SMT-LIB (Satisfiability Modulo Theories Library) and OMT (Optimization Modulo Theories) formulas. The library implements an efficient Directed Acyclic Graph (DAG) representation for formulas, enabling comprehensive support for various SMT theories and optimization problems.

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
<!-- - **Model Generation and Manipulation** - Create and manipulate models representing variable assignments
- **Smart Pointer Integration** - All major components use std::shared_ptr for safe memory management
- **Thread-Safe Implementation** - Safe for use in multi-threaded applications -->

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
git clone https://github.com/fuqi-jia/SMTLIBParser.git
cd SMTLIBParser

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

For projects using Git, SMTLIBParser can be included as a submodule:

```bash
# Add the repository as a submodule
git submodule add https://github.com/fuqi-jia/SMTLIBParser.git SMTLIBParser

# Initialize the submodule
git submodule update --init --recursive

# Update the submodule to the latest version when needed
git submodule update --remote --merge
```

### Build Configuration Options

| Option | Description | Default |
|--------|-------------|---------|
| `BUILD_SHARED_LIBS` | Build shared libraries (.so/.dll) | OFF |
| `BUILD_BOTH_LIBS` | Build both static (.a/.lib) and shared libraries | ON |

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
    SMTLIBParser::Parser parser;

    // Parse an SMT-LIB2 file
    if (!parser.parse("formula.smt2")) {
        std::cerr << "Error parsing file" << std::endl;
        return 1;
    }

    // Retrieve the parsed assertions
    auto assertions = parser.getAssertions();

    // Output the assertions
    for(auto constraint: assertions){
        std::cout << dumpSMTLIB2(constraint) << std::endl;
    }

    return 0;
}
```

### Using Smart Pointers and Factory Methods

```cpp
#include "parser.h"
#include "model.h"
#include <iostream>

int main() {
    // Create a parser using factory method
    auto parser = SMTLIBParser::newParser();
    
    // Alternative: create a parser with file in one step
    auto fileParser = SMTLIBParser::newParser("formula.smt2");
    
    // Create a model
    auto model = SMTLIBParser::newModel();
    
    // Create and manipulate variables
    auto x = parser->mkVarInt("x");
    auto y = parser->mkVarInt("y");
    
    // Add assignments to model
    model->add(x, parser->mkConstInt(10));
    model->add(y, parser->mkConstInt(20));
    
    // Evaluate expressions using the model
    auto expr = parser->mkAdd({x, y});
    auto result = parser->evaluate(expr, model);
    
    std::cout << "x + y = " << dumpSMTLIB2(expr) << std::endl;
    
    return 0;
}
```

### Constructing Expressions Programmatically

```cpp
#include "parser.h"
#include <iostream>

int main() {
    // Initialize the parser engine
    SMTLIBParser::Parser parser;

    // Create integer variables
    auto x = parser.mkVar(INT_SORT, "x");
    auto y = parser.mkVarInt("y");

    // Construct the expression: (x + y) > 10
    auto sum = parser.mkAdd({x, y});
    auto constant = parser.mkConstInt(10);
    auto constraint = parser.mkGt(sum, constant);

    // Output SMT-LIB2 representation
    std::cout << dumpSMTLIB2(constraint) << std::endl;
    // Output: (> (+ x y) 10)

    return 0;
}
```

### Compiling Client Applications

When building applications that use SMTLIBParser, link against the library and its dependencies:

```bash
g++ -std=c++17 -o application main.cpp -lsmtlibparser -lgmp
```

### Complete Project Example

For a complete project example, check out [SMTLIBParser-Test](https://github.com/fuqi-jia/SMTLIBParser-Test) which demonstrates how to integrate and use the library as a Git submodule.

#### Project Structure:
```
SMTLIBParser-Test/
├── CMakeLists.txt          # Build configuration
├── SMTLIBParser/           # Submodule
├── src/                    # Application source code
│   └── main.cpp
└── test/                   # Test SMT-LIB2 files
    └── 1.smt2
```

#### Setting Up the Project:

1. Clone the repository and initialize the submodule:
```bash
git clone https://github.com/fuqi-jia/SMTLIBParser-Test.git
cd SMTLIBParser-Test
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
./SMTLIBParser_Test ../test/1.smt2
```

This simple example demonstrates how to parse and process an SMT-LIB2 file. You can use this project as a template for your own applications.

## API Reference

### Core Components and Smart Pointer Types

| Component | Smart Pointer Type | Description |
|-----------|-------------------|-------------|
| `Parser` | `ParserPtr` | Main class for parsing SMT-LIB2 files and managing expressions |
| `DAGNode` | `NodePtr` | Represents expressions as nodes in a directed acyclic graph |
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
| Constant Creation | `mkConst`, `mkConstInt`, `mkConstReal`, `mkTrue`, `mkFalse`, `...` |
| Expression Building | `mkOper`, `mkEq`, `mkDistinct`, `mkNot`, `mkAnd`, `mkOr`, `...` |
| Arithmetic Operations | `mkAdd`, `mkSub`, `mkMul`, `mkDiv`, `mkPow`, `...` |
| Comparison Operations | `mkLt`, `mkLe`, `mkGt`, `mkGe`, `...` |
| Bitvector Operations | `mkBvAnd`, `mkBvOr`, `mkBvXor`, `mkBvAdd`, `mkBvShl`, `...` |
| String Operations | `mkStrLen`, `mkStrConcat`, `mkStrSubstr`, `mkStrIndexof`, `...` |
| Regular Expression Operations | `mkStrToReg`, `mkRegUnion`, `mkRegStar`, `...` |
| Array Operations | `mkSelect`, `mkStore` |
| Floating Point Operations | `mkFpAdd`, `mkFpMul`, `mkFpDiv`, `mkFpEq`, `...` |
| Model Operations | `add`, `get`, `...` |

## Supported Theories

### Core Theory
- Full Boolean algebra: `and`, `or`, `not`, `implies`, `xor`
- Equality and distinctness predicates

### Arithmetic Theory
- Integer and Real arithmetic
- Arithmetic operations: addition, subtraction, multiplication, division
- Comparison relations: <, ≤, >, ≥
- Transcendental functions: exponential, logarithm, trigonometric functions
- Special functions: absolute value, modulo, power, square root

### Bitvector Theory
- Bit-level operations: `and`, `or`, `xor`, `not`, `nand`, `nor`, `xnor`
- Arithmetic operations: addition, subtraction, multiplication, division
- Comparison relations: unsigned/signed less than, greater than
- Bit manipulation: shift, rotate, concatenation, extraction
- Conversion operations: to/from integers, sign extension

### Floating Point Theory
- IEEE-754 compliant arithmetic operations
- Special value detection: `isNaN`, `isInfinite`, `isZero`
- Rounding modes support
- Conversion operations to/from other types

### String Theory
- String operations: concatenation, length, substring, indexing
- Regular expression operations: union, intersection, Kleene star
- String predicates: contains, prefix, suffix
- Conversion functions: to/from integers, to/from code points

### Array Theory
- Multi-dimensional array support
- Select and store operations
- Array extensionality

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Development Status

**Active Development** - This project is under continuous improvement and development. New features and optimizations are being added regularly.

## Contact

For technical inquiries or support, please contact:

**Fuqi Jia**  
Email: jiafq@ios.ac.cn  
Institute of Software, Chinese Academy of Sciences
