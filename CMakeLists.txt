cmake_minimum_required(VERSION 3.10)
project(SMTParser VERSION 1.0.0 LANGUAGES CXX)

# set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# set build type
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# add options
option(BUILD_SHARED_LIBS "Build shared libraries (.so/.dll)" OFF)
option(BUILD_BOTH_LIBS "Build both static and shared libraries" ON)
option(BUILD_TESTS "Build the tests" ON)

# find dependencies
find_package(Boost REQUIRED COMPONENTS system)

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

# collect all source files, excluding test directory
file(GLOB_RECURSE SOURCES "src/*.cpp")

# collect all header files
file(GLOB_RECURSE HEADERS "include/*.h")

# create library
if(BUILD_BOTH_LIBS)
    # create static library
    add_library(smtlib_parser_static STATIC ${SOURCES} ${HEADERS})
    set_target_properties(smtlib_parser_static PROPERTIES 
        OUTPUT_NAME smtlib_parser
        POSITION_INDEPENDENT_CODE ON
    )
    
    # set static library include directories
    target_include_directories(smtlib_parser_static PUBLIC 
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Boost_INCLUDE_DIRS}
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link static library dependencies
    target_link_libraries(smtlib_parser_static PUBLIC
        Boost::system
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # create shared library
    add_library(smtlib_parser_shared SHARED ${SOURCES} ${HEADERS})
    set_target_properties(smtlib_parser_shared PROPERTIES 
        OUTPUT_NAME smtlib_parser
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
    )
    
    # set shared library include directories
    target_include_directories(smtlib_parser_shared PUBLIC 
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Boost_INCLUDE_DIRS}
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link shared library dependencies
    target_link_libraries(smtlib_parser_shared PUBLIC
        Boost::system
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # create alias target for compatibility
    add_library(smtlib_parser ALIAS smtlib_parser_static)
    
    # install configuration
    install(TARGETS smtlib_parser_static smtlib_parser_shared
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
    )
else()
    # create single library (static or shared, depending on BUILD_SHARED_LIBS)
    add_library(smtlib_parser ${SOURCES} ${HEADERS})
    
    # set library include directories
    target_include_directories(smtlib_parser PUBLIC 
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Boost_INCLUDE_DIRS}
        ${GMP_INCLUDE_DIRS}
        ${MPFR_INCLUDE_DIRS}
    )
    
    # link library dependencies
    target_link_libraries(smtlib_parser PUBLIC
        Boost::system
        ${GMP_LIBRARIES}
        ${MPFR_LIBRARIES}
    )
    
    # install configuration
    install(TARGETS smtlib_parser
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
    )
endif()

# install header files
install(DIRECTORY include/ DESTINATION include/smtlib_parser)

# if needed, add test subdirectory
if(BUILD_TESTS)
    add_subdirectory(test)
endif() 