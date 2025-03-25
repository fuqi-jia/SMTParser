cmake_minimum_required(VERSION 3.10)
project(SMTParser VERSION 1.0.0 LANGUAGES CXX)

# 设置C++标准
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 添加选项：BUILD_SHARED_LIBS
option(BUILD_SHARED_LIBS "Build shared libraries" OFF)

# 查找依赖包
find_package(Boost REQUIRED COMPONENTS system)

# 查找GMP库
find_package(PkgConfig REQUIRED)
pkg_check_modules(GMP REQUIRED gmp)

if(NOT GMP_FOUND)
    # 如果pkg-config找不到，尝试使用环境变量
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

# 设置库名称
set(LIB_NAME "smtparser")

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
    src/dag.h
    src/util.h
    src/objective.h
    src/kind.h
    src/sort.h
    src/options.h
)

# 创建include目录
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include)

# 复制头文件到构建目录
foreach(header ${PUBLIC_HEADERS})
    file(COPY ${header} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/include)
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
set_target_properties(${LIB_NAME} PROPERTIES
    VERSION ${PROJECT_VERSION}
    SOVERSION ${PROJECT_VERSION_MAJOR}
    PUBLIC_HEADER ${PUBLIC_HEADERS}
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN YES
)

# 设置包含目录
target_include_directories(${LIB_NAME}
    PUBLIC
        ${INCLUDE_DIRS}
)

# 链接依赖库
target_link_libraries(${LIB_NAME}
    PUBLIC
        ${Boost_LIBRARIES}
        ${GMP_LIBRARIES}
)

# 安装规则
install(TARGETS ${LIB_NAME}
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    PUBLIC_HEADER DESTINATION include
)

# 添加编译选项
if(MSVC)
    target_compile_options(${LIB_NAME} PRIVATE /W4)
else()
    target_compile_options(${LIB_NAME} PRIVATE -Wall -Wextra -Wpedantic)
endif()

# 设置输出目录
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib) 