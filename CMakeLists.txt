cmake_minimum_required(VERSION 3.10)
project(SMTParser VERSION 1.0.0 LANGUAGES CXX)

# set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -O3 -Wall -Wextra -Werror")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unused-but-set-variable -Wno-unused-value")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unused-local-typedefs")

# set build type
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# add options
option(BUILD_SHARED_LIBS "Build shared libraries (.so/.dll)" OFF)
option(BUILD_BOTH_LIBS "Build both static and shared libraries" ON)
option(BUILD_TESTS "Build the tests" OFF)
option(BUILD_NL2SMT "Build NL2SMT frontend into smtparser" OFF)
option(ENABLE_DEBUG_SYMBOLS "Enable debug symbols for GDB support" OFF)
option(ENABLE_TIMING "Enable timing profiler" OFF)

# enable time functions
if(ENABLE_TIMING)
    add_compile_definitions(ENABLE_TIMING)
endif()

# use pkg-config to find GMP and MPFR
find_package(PkgConfig REQUIRED)
pkg_check_modules(GMP REQUIRED gmp)
pkg_check_modules(MPFR REQUIRED mpfr)

# if pkg-config doesn't find the libraries, try manually finding them
if(NOT GMP_FOUND)
    # try searching for library files directly
    find_library(GMP_LIBRARIES NAMES gmp libgmp)
    find_path(GMP_INCLUDE_DIRS NAMES gmp.h)
    if(GMP_LIBRARIES AND GMP_INCLUDE_DIRS)
        set(GMP_FOUND TRUE)
    else()
        message(FATAL_ERROR "GMP library not found. Please install GMP development package.")
    endif()
endif()

if(NOT MPFR_FOUND)
    # try searching for library files directly
    find_library(MPFR_LIBRARIES NAMES mpfr libmpfr)
    find_path(MPFR_INCLUDE_DIRS NAMES mpfr.h)
    if(MPFR_LIBRARIES AND MPFR_INCLUDE_DIRS)
        set(MPFR_FOUND TRUE)
    else()
        message(FATAL_ERROR "MPFR library not found. Please install MPFR development package.")
    endif()
endif()

# collect all source files
file(GLOB_RECURSE SOURCES "src/*.cpp")

# collect all header files
file(GLOB_RECURSE HEADERS "include/*.h")

# create library
if(BUILD_BOTH_LIBS)
    # create static library
    add_library(smtparser_static STATIC ${SOURCES} ${HEADERS})
    set_target_properties(smtparser_static PROPERTIES 
        OUTPUT_NAME smtparser
        POSITION_INDEPENDENT_CODE ON
    )
    
    if(ENABLE_DEBUG_SYMBOLS)
        target_compile_options(smtparser_static PRIVATE -g -O0)
    endif()
    
    # set static library include directories
    target_include_directories(smtparser_static PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link static library dependencies
    target_link_libraries(smtparser_static PUBLIC
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # create shared library
    add_library(smtparser_shared SHARED ${SOURCES} ${HEADERS})
    set_target_properties(smtparser_shared PROPERTIES 
        OUTPUT_NAME smtparser
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
    )
    
    if(ENABLE_DEBUG_SYMBOLS)
        target_compile_options(smtparser_shared PRIVATE -g -O0)
    endif()
    
    # set shared library include directories
    target_include_directories(smtparser_shared PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link shared library dependencies
    target_link_libraries(smtparser_shared PUBLIC
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # create alias target for compatibility
    add_library(smtparser ALIAS smtparser_static)
    
    # install configuration
    install(TARGETS smtparser_static smtparser_shared
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
    )
else()
    # create single library (static or shared, depending on BUILD_SHARED_LIBS)
    add_library(smtparser ${SOURCES} ${HEADERS})
    
    if(ENABLE_DEBUG_SYMBOLS)
        target_compile_options(smtparser PRIVATE -g -O0)
    endif()
    
    # set library include directories (single lib branch)
    target_include_directories(smtparser PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link library dependencies
    target_link_libraries(smtparser PUBLIC
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # install configuration
    install(TARGETS smtparser
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
    )
endif()

# install header files
install(DIRECTORY include/ DESTINATION include/smtparser)

# smtparser: unified CLI (parser / solver / nl when BUILD_NL2SMT)
set(APPS_INCLUDES
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_SOURCE_DIR}/apps
    ${GMP_INCLUDE_DIRS}
    ${MPFR_INCLUDE_DIRS}
)
set(SMTPARSER_EXE_SOURCES
    apps/main.cpp
    apps/config/config_loader.cpp
    apps/parser/run_parser.cpp
    apps/solver/run_solver.cpp
)
if(BUILD_NL2SMT)
    list(APPEND SMTPARSER_EXE_SOURCES
        apps/nl2smt/llm_caller.cpp
        apps/nl2smt/nl2smt.cpp
    )
endif()
add_executable(smtparser_exe ${SMTPARSER_EXE_SOURCES})
set_target_properties(smtparser_exe PROPERTIES OUTPUT_NAME smtparser)
target_include_directories(smtparser_exe PRIVATE ${APPS_INCLUDES})
if(BUILD_NL2SMT)
    target_compile_definitions(smtparser_exe PRIVATE BUILD_NL2SMT)
endif()
target_link_libraries(smtparser_exe PRIVATE smtparser ${GMP_LIBRARIES} ${MPFR_LIBRARIES})
install(TARGETS smtparser_exe RUNTIME DESTINATION bin)

# NL2SMT demo and test (only when BUILD_NL2SMT)
if(BUILD_NL2SMT)
    set(NL2SMT_SOURCES apps/nl2smt/llm_caller.cpp apps/nl2smt/nl2smt.cpp)
    add_executable(demo_nl2smt apps/nl2smt/demo_nl2smt.cpp ${NL2SMT_SOURCES})
    target_include_directories(demo_nl2smt PRIVATE ${APPS_INCLUDES})
    target_link_libraries(demo_nl2smt PRIVATE smtparser ${GMP_LIBRARIES} ${MPFR_LIBRARIES})

    add_executable(test_nl2smt apps/nl2smt/test_nl2smt.cpp ${NL2SMT_SOURCES})
    target_include_directories(test_nl2smt PRIVATE ${APPS_INCLUDES})
    target_compile_definitions(test_nl2smt PRIVATE "NL2SMT_MOCK_SCRIPT_PATH=\"${CMAKE_CURRENT_SOURCE_DIR}/apps/nl2smt/mock_llm.sh\"")
    target_link_libraries(test_nl2smt PRIVATE smtparser ${GMP_LIBRARIES} ${MPFR_LIBRARIES})
endif()

# if needed, add test subdirectory
if(BUILD_TESTS)
    add_subdirectory(test)
endif() 