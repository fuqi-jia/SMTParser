cmake_minimum_required(VERSION 2.8.12)
project(SMTLIBParser CXX)

# 设置CMake策略
if(CMAKE_VERSION VERSION_GREATER "3.3")
    cmake_policy(SET CMP0063 NEW)
endif()

# 设置C++标准
if(CMAKE_VERSION VERSION_GREATER "3.1")
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
else()
    if(MSVC)
        add_definitions(-D_CRT_SECURE_NO_WARNINGS)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /std:c++17")
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++17")
    endif()
endif()

# 添加选项：BUILD_SHARED_LIBS
option(BUILD_SHARED_LIBS "Build shared libraries" OFF)

# 查找依赖包
if(CMAKE_VERSION VERSION_GREATER "3.5")
    find_package(Boost REQUIRED COMPONENTS system)
else()
    # 对于低版本CMake，使用更基础的查找方式
    find_package(Boost REQUIRED)
    if(NOT Boost_FOUND)
        message(FATAL_ERROR "Boost library not found")
    endif()
endif()

# 查找GMP库
if(UNIX)
    find_package(PkgConfig REQUIRED)
    pkg_check_modules(GMP REQUIRED gmp)
else()
    # Windows下使用环境变量
    if(DEFINED ENV{GMP_DIR})
        set(GMP_INCLUDE_DIRS $ENV{GMP_DIR}/include)
        set(GMP_LIBRARY_DIRS $ENV{GMP_DIR}/lib)
        set(GMP_LIBRARIES gmp)
        set(GMP_FOUND TRUE)
    else()
        message(FATAL_ERROR "GMP library not found. Please set GMP_DIR environment variable")
    endif()
endif()

# 设置库名称
set(LIB_NAME "smtlibparser")

# 添加源文件
set(SOURCES
    src/base_parser.cpp
    src/op_parser.cpp
    src/opt_parser.cpp
    src/dag.cpp
    src/util.cpp
    src/objective.cpp
    src/kind.cpp
    src/sort.cpp
)

# 定义公共头文件
set(PUBLIC_HEADERS
    include/parser.h
    include/dag.h
    include/util.h
    include/objective.h
    include/kind.h
    include/sort.h
    include/options.h
)

# 创建include目录
if(CMAKE_VERSION VERSION_GREATER "3.0")
    file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include)
else()
    file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/include")
endif()

# 复制头文件到构建目录
foreach(header ${PUBLIC_HEADERS})
    if(CMAKE_VERSION VERSION_GREATER "3.0")
        file(COPY ${header} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/include)
    else()
        file(COPY "${header}" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/include")
    endif()
endforeach()

# 添加头文件目录
set(INCLUDE_DIRS
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_BINARY_DIR}/include
    ${Boost_INCLUDE_DIRS}
    ${GMP_INCLUDE_DIRS}
)

# 创建库
add_library(${LIB_NAME} ${SOURCES})

# 设置库的属性
if(CMAKE_VERSION VERSION_GREATER "3.0")
    set_target_properties(${LIB_NAME} PROPERTIES
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
        PUBLIC_HEADER "${PUBLIC_HEADERS}"
        CXX_VISIBILITY_PRESET hidden
        VISIBILITY_INLINES_HIDDEN YES
    )
else()
    set_target_properties(${LIB_NAME} PROPERTIES
        VERSION ${PROJECT_VERSION}
        SOVERSION ${PROJECT_VERSION_MAJOR}
        PUBLIC_HEADER "${PUBLIC_HEADERS}"
    )
endif()

# 设置包含目录
if(CMAKE_VERSION VERSION_GREATER "3.0")
    target_include_directories(${LIB_NAME}
        PUBLIC
            ${INCLUDE_DIRS}
    )
else()
    include_directories(${INCLUDE_DIRS})
endif()

# 链接依赖库
if(CMAKE_VERSION VERSION_GREATER "3.0")
    target_link_libraries(${LIB_NAME}
        PUBLIC
            ${Boost_LIBRARIES}
            ${GMP_LIBRARIES}
    )
else()
    target_link_libraries(${LIB_NAME}
        ${Boost_LIBRARIES}
        ${GMP_LIBRARIES}
    )
endif()

# 安装规则
install(TARGETS ${LIB_NAME}
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    PUBLIC_HEADER DESTINATION include
)

# 添加编译选项
if(MSVC)
    if(CMAKE_VERSION VERSION_GREATER "3.0")
        target_compile_options(${LIB_NAME} PRIVATE /W4)
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W4")
    endif()
else()
    if(CMAKE_VERSION VERSION_GREATER "3.0")
        target_compile_options(${LIB_NAME} PRIVATE -Wall -Wextra -Wpedantic)
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic")
    endif()
endif()

# 设置输出目录
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib) 