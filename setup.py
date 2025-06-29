#!/usr/bin/env python3
"""
Setup script for SMTParser Python bindings

This script builds and installs the SMTParser Python extension module
using pybind11 and the existing C++ SMTParser library.

Requirements:
- pybind11
- CMake
- GMP library
- MPFR library

Usage:
    python setup.py build_ext --inplace  # Build in place
    python setup.py install              # Install system-wide
    pip install .                        # Install with pip
"""

import os
import sys
import subprocess
import glob
from pathlib import Path

import pybind11
from pybind11.setup_helpers import Pybind11Extension, build_ext
from pybind11 import get_cmake_dir

__version__ = "1.0.0"

# Find all source files
def find_source_files():
    """Find all C++ source files for the library"""
    src_files = []
    
    # Add all source files from src directory
    src_dir = Path("src")
    if src_dir.exists():
        src_files.extend(glob.glob("src/*.cpp"))
    
    # Add the Python binding file
    src_files.append("python_binding/smtparser_py.cpp") 
    
    return src_files

# Find include directories
def find_include_dirs():
    """Find all include directories"""
    include_dirs = [
        "include",
        pybind11.get_include(),
    ]
    
    # Try to find GMP and MPFR include directories
    gmp_include_dirs = [
        "/usr/include",
        "/usr/local/include", 
        "/opt/local/include",
        "/mingw64/include",  # MSYS2
    ]
    
    # Add any existing include directories
    for inc_dir in gmp_include_dirs:
        if os.path.exists(os.path.join(inc_dir, "gmp.h")):
            include_dirs.append(inc_dir)
            break
            
    for inc_dir in gmp_include_dirs:
        if os.path.exists(os.path.join(inc_dir, "mpfr.h")):
            if inc_dir not in include_dirs:
                include_dirs.append(inc_dir)
            break
    
    return include_dirs

# Find library directories and libraries
def find_libraries():
    """Find required libraries"""
    libraries = ["gmp", "mpfr"]
    library_dirs = []
    
    # Common library directories
    lib_dirs = [
        "/usr/lib",
        "/usr/local/lib",
        "/opt/local/lib", 
        "/mingw64/lib",  # MSYS2
        "/usr/lib/x86_64-linux-gnu",  # Ubuntu/Debian
    ]
    
    for lib_dir in lib_dirs:
        if os.path.exists(lib_dir):
            # Check if GMP library exists in this directory
            if (os.path.exists(os.path.join(lib_dir, "libgmp.so")) or 
                os.path.exists(os.path.join(lib_dir, "libgmp.a")) or
                os.path.exists(os.path.join(lib_dir, "libgmp.dll.a"))):
                library_dirs.append(lib_dir)
                break
    
    return libraries, library_dirs

# Setup compiler flags
def get_compile_args():
    """Get compilation arguments"""
    compile_args = ["-std=c++17"]
    
    # Add optimization flags for release builds
    if not os.environ.get("DEBUG"):
        compile_args.extend(["-O3", "-DNDEBUG"])
    else:
        compile_args.extend(["-g", "-O0"])
    
    # Platform-specific flags
    if sys.platform.startswith("win"):
        compile_args.extend(["-DWIN32", "-D_WIN32"])
    elif sys.platform.startswith("darwin"):
        compile_args.extend(["-mmacosx-version-min=10.9"])
    
    return compile_args

def get_link_args():
    """Get linking arguments"""
    link_args = []
    
    # Platform-specific linking flags
    if sys.platform.startswith("darwin"):
        link_args.extend(["-mmacosx-version-min=10.9"])
    
    return link_args

# Create the extension module
def create_extension():
    """Create the pybind11 extension"""
    source_files = find_source_files()
    include_dirs = find_include_dirs()
    libraries, library_dirs = find_libraries()
    compile_args = get_compile_args()
    link_args = get_link_args()
    
    ext = Pybind11Extension(
        "smtparser",
        source_files,
        include_dirs=include_dirs,
        libraries=libraries,
        library_dirs=library_dirs,
        cxx_std=17,
        extra_compile_args=compile_args,
        extra_link_args=link_args,
    )
    
    return ext

# Custom build_ext class to handle build dependencies
class CustomBuildExt(build_ext):
    """Custom build extension to handle library dependencies"""
    
    def run(self):
        # Check for required dependencies
        self.check_dependencies()
        super().run()
    
    def check_dependencies(self):
        """Check if required dependencies are available"""
        try:
            import pybind11
        except ImportError:
            raise RuntimeError("pybind11 is required to build this package")
        
        # Check for GMP and MPFR headers
        gmp_found = False
        mpfr_found = False
        
        for inc_dir in ["/usr/include", "/usr/local/include", "/opt/local/include", "/mingw64/include"]:
            if os.path.exists(os.path.join(inc_dir, "gmp.h")):
                gmp_found = True
            if os.path.exists(os.path.join(inc_dir, "mpfr.h")):
                mpfr_found = True
        
        if not gmp_found:
            print("Warning: GMP headers not found. Make sure libgmp-dev is installed.")
        if not mpfr_found:
            print("Warning: MPFR headers not found. Make sure libmpfr-dev is installed.")

if __name__ == "__main__":
    from setuptools import setup
    
    # Create extension
    ext_modules = [create_extension()]
    
    setup(
        name="smtparser",
        version=__version__,
        author="SMTParser Python Binding",
        author_email="",
        url="https://github.com/fuqi-jia/SMTParser",
        description="Python bindings for SMTParser - SMT-LIB2 parser and expression builder",
        long_description="""
        SMTParser Python Bindings
        =========================
        
        Python bindings for the SMTParser C++ library, providing:
        
        - SMT-LIB2 file parsing and processing
        - Programmatic expression building
        - Support for multiple SMT theories (Boolean, Arithmetic, Bitvector, etc.)
        - Model evaluation and constraint solving interface
        - Optimization Modulo Theories (OMT) support
        
        Requirements:
        - Python 3.6+
        - GMP library (libgmp-dev)
        - MPFR library (libmpfr-dev)
        """,
        long_description_content_type="text/plain",
        ext_modules=ext_modules,
        cmdclass={"build_ext": CustomBuildExt},
        zip_safe=False,
        python_requires=">=3.6",
        install_requires=[
            "pybind11>=2.6.0",
        ],
        classifiers=[
            "Development Status :: 4 - Beta",
            "Intended Audience :: Developers",
            "Intended Audience :: Science/Research",
            "License :: OSI Approved :: MIT License",
            "Programming Language :: Python :: 3",
            "Programming Language :: Python :: 3.6",
            "Programming Language :: Python :: 3.7", 
            "Programming Language :: Python :: 3.8",
            "Programming Language :: Python :: 3.9",
            "Programming Language :: Python :: 3.10",
            "Programming Language :: Python :: 3.11",
            "Programming Language :: C++",
            "Topic :: Scientific/Engineering :: Mathematics",
            "Topic :: Software Development :: Libraries :: Python Modules",
        ],
        keywords="smt smt-lib2 parser satisfiability modulo theories optimization",
    ) 