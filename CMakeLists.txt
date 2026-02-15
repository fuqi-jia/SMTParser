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

# Optional NL2SMT: only when BUILD_NL2SMT=ON (default OFF, no third-party deps)
if(BUILD_NL2SMT)
    include(FetchContent)
    FetchContent_Declare(json URL https://github.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz)
    FetchContent_MakeAvailable(json)
    FetchContent_Declare(httplib
        GIT_REPOSITORY https://github.com/yhirose/cpp-httplib
        GIT_TAG v0.14.3)
    FetchContent_MakeAvailable(httplib)
    message(STATUS "NL2SMT enabled. For natural-language tests, start the LLM proxy first: ./llm.sh")
endif()

# collect all source files (exclude nl2smt.cpp when BUILD_NL2SMT=OFF)
file(GLOB_RECURSE SOURCES "src/*.cpp")
if(NOT BUILD_NL2SMT)
    list(FILTER SOURCES EXCLUDE REGEX ".*/nl2smt\\.cpp$")
endif()

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
    if(BUILD_NL2SMT)
        target_compile_definitions(smtparser_static PUBLIC SMTLIBPARSER_ENABLE_NL2SMT)
        target_include_directories(smtparser_static PRIVATE ${httplib_SOURCE_DIR})
        target_link_libraries(smtparser_static PUBLIC nlohmann_json::nlohmann_json)
    endif()
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
    if(BUILD_NL2SMT)
        target_compile_definitions(smtparser_shared PUBLIC SMTLIBPARSER_ENABLE_NL2SMT)
        target_include_directories(smtparser_shared PRIVATE ${httplib_SOURCE_DIR})
        target_link_libraries(smtparser_shared PUBLIC nlohmann_json::nlohmann_json)
    endif()
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
    if(BUILD_NL2SMT)
        target_compile_definitions(smtparser PUBLIC SMTLIBPARSER_ENABLE_NL2SMT)
        target_include_directories(smtparser PRIVATE ${httplib_SOURCE_DIR})
        target_link_libraries(smtparser PUBLIC nlohmann_json::nlohmann_json)
    endif()
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
    apps/features/run_features.cpp
    apps/solver/run_solver.cpp
)
if(BUILD_NL2SMT)
    list(APPEND SMTPARSER_EXE_SOURCES apps/nl2smt/run_nl2smt.cpp)
endif()
add_executable(smtparser_exe ${SMTPARSER_EXE_SOURCES})
set_target_properties(smtparser_exe PROPERTIES OUTPUT_NAME smtparser)
target_include_directories(smtparser_exe PRIVATE ${APPS_INCLUDES})
if(BUILD_NL2SMT)
    target_compile_definitions(smtparser_exe PRIVATE BUILD_NL2SMT SMTLIBPARSER_ENABLE_NL2SMT)
endif()
target_link_libraries(smtparser_exe PRIVATE smtparser ${GMP_LIBRARIES} ${MPFR_LIBRARIES})
install(TARGETS smtparser_exe RUNTIME DESTINATION bin)

# if needed, add test subdirectory
if(BUILD_TESTS)
    add_subdirectory(test)
endif() 