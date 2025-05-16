cmake_minimum_required(VERSION 3.10)
project(SMTParser VERSION 1.0.0 LANGUAGES CXX)

# set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# add option: BUILD_SHARED_LIBS
option(BUILD_SHARED_LIBS "Build shared libraries" OFF)
# add option: BUILD_BOTH_LIBS
option(BUILD_BOTH_LIBS "Build both static and shared libraries" ON)

# find dependencies
find_package(Boost REQUIRED COMPONENTS system)

# find GMP library
find_package(PkgConfig REQUIRED)
pkg_check_modules(GMP REQUIRED gmp)

if(NOT GMP_FOUND)
    # if pkg-config not found, try using environment variable
    if(DEFINED ENV{GMP_DIR})
        set(GMP_INCLUDE_DIRS $ENV{GMP_DIR}/include)
        set(GMP_LIBRARY_DIRS $ENV{GMP_DIR}/lib)
        set(GMP_LIBRARIES gmp)
        set(GMP_FOUND TRUE)
    else()
        message(FATAL_ERROR "GMP library not found. Please install GMP and either:\n"
                          "1. Install pkg-config and ensure GMP is properly installed\n"
                          "2. Set GMP_DIR environment variable to point to GMP installation directory")
    endif()
endif()

# find MPFR library
pkg_check_modules(MPFR REQUIRED mpfr)

if(NOT MPFR_FOUND)
    # if pkg-config not found, try using environment variable
    if(DEFINED ENV{MPFR_DIR})
        set(MPFR_INCLUDE_DIRS $ENV{MPFR_DIR}/include)
        set(MPFR_LIBRARY_DIRS $ENV{MPFR_DIR}/lib)
        set(MPFR_LIBRARIES mpfr)
        set(MPFR_FOUND TRUE)
    else()
        message(FATAL_ERROR "MPFR library not found. Please install MPFR and either:\n"
                          "1. Install pkg-config and ensure MPFR is properly installed\n"
                          "2. Set MPFR_DIR environment variable to point to MPFR installation directory")
    endif()
endif()

# set library name
set(LIB_NAME "smtlibparser")

# add source files
set(SOURCES
    src/base_parser.cpp
    src/eval_parser.cpp
    src/op_parser.cpp
    src/opt_parser.cpp
    src/dag.cpp
    src/util.cpp
    src/objective.cpp
    src/kind.cpp
    src/sort.cpp
    src/model.cpp
    src/number.cpp
)

# define public headers
set(PUBLIC_HEADERS
    include/parser.h
    include/dag.h
    include/util.h
    include/objective.h
    include/kind.h
    include/sort.h
    include/options.h
    include/model.h
    include/number.h
)

# create include directory
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include)

# copy headers to build directory
foreach(header ${PUBLIC_HEADERS})
    file(COPY ${header} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/include)
endforeach()

# add header file directories
set(INCLUDE_DIRS
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_BINARY_DIR}/include
    ${Boost_INCLUDE_DIRS}
    ${GMP_INCLUDE_DIRS}
    ${MPFR_INCLUDE_DIRS}
)

# create library
if(BUILD_BOTH_LIBS)
    # create static library
    add_library(${LIB_NAME}_static STATIC ${SOURCES})
    set_target_properties(${LIB_NAME}_static PROPERTIES 
        OUTPUT_NAME ${LIB_NAME}
        VERSION ${PROJECT_VERSION}
        PUBLIC_HEADER "${PUBLIC_HEADERS}"
        CXX_VISIBILITY_PRESET hidden
        VISIBILITY_INLINES_HIDDEN YES
    )
    target_include_directories(${LIB_NAME}_static PUBLIC ${INCLUDE_DIRS})
    target_link_libraries(${LIB_NAME}_static PUBLIC ${Boost_LIBRARIES} ${GMP_LIBRARIES} ${MPFR_LIBRARIES})

    # create dynamic library
    add_library(${LIB_NAME}_shared SHARED ${SOURCES})
    set_target_properties(${LIB_NAME}_shared PROPERTIES 
        OUTPUT_NAME ${LIB_NAME}
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
        PUBLIC_HEADER "${PUBLIC_HEADERS}"
        CXX_VISIBILITY_PRESET hidden
        VISIBILITY_INLINES_HIDDEN YES
    )
    target_include_directories(${LIB_NAME}_shared PUBLIC ${INCLUDE_DIRS})
    target_link_libraries(${LIB_NAME}_shared PUBLIC ${Boost_LIBRARIES} ${GMP_LIBRARIES} ${MPFR_LIBRARIES})

    # add compile options
    if(MSVC)
        target_compile_options(${LIB_NAME}_static PRIVATE /W4)
        target_compile_options(${LIB_NAME}_shared PRIVATE /W4)
    else()
        target_compile_options(${LIB_NAME}_static PRIVATE -Wall -Wextra -Wpedantic)
        target_compile_options(${LIB_NAME}_shared PRIVATE -Wall -Wextra -Wpedantic)
    endif()

    # install rules
    install(TARGETS ${LIB_NAME}_static ${LIB_NAME}_shared
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib
        RUNTIME DESTINATION bin
        PUBLIC_HEADER DESTINATION include
    )
else()
    # create single library (static or dynamic depending on BUILD_SHARED_LIBS option)
    add_library(${LIB_NAME} ${SOURCES})

    # set library properties
    set_target_properties(${LIB_NAME} PROPERTIES
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
        PUBLIC_HEADER "${PUBLIC_HEADERS}"
        CXX_VISIBILITY_PRESET hidden
        VISIBILITY_INLINES_HIDDEN YES
    )

    # set include directories
    target_include_directories(${LIB_NAME}
        PUBLIC
            ${INCLUDE_DIRS}
    )

    # link dependencies
    target_link_libraries(${LIB_NAME}
        PUBLIC
            ${Boost_LIBRARIES}
            ${GMP_LIBRARIES}
            ${MPFR_LIBRARIES}
    )

    # install rules
    install(TARGETS ${LIB_NAME}
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib
        RUNTIME DESTINATION bin
        PUBLIC_HEADER DESTINATION include
    )

    # add compile options
    if(MSVC)
        target_compile_options(${LIB_NAME} PRIVATE /W4)
    else()
        target_compile_options(${LIB_NAME} PRIVATE -Wall -Wextra -Wpedantic)
    endif()
endif()

# set output directories
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib) 