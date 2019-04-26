# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

cmake_minimum_required(VERSION 3.5)

include(cmake/cable/bootstrap.cmake)

include(CableCompilerSettings)
include(CableToolchains)
include(CMakePackageConfigHelpers)
include(GNUInstallDirs)

option(INTX_TESTING "Build intx with tests" ON)
option(INTX_BENCHMARKING "Build intx with benchmark tools" ON)
option(INTX_FUZZING "Build intx fuzzers" OFF)

cable_configure_toolchain(DEFAULT cxx14)

include(Hunter/init)

project(intx)
set(PROJECT_VERSION 0.1.0)

cable_configure_compiler(NO_PEDANTIC NO_CONVERSION_WARNINGS NO_STACK_PROTECTION)

if(INTX_TESTING)
    enable_testing()
endif()

if(INTX_FUZZING)
    set(fuzzing_flags -fsanitize=fuzzer-no-link,undefined,address)
    add_compile_options(${fuzzing_flags})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${fuzzing_flags}")
endif()

option(NATIVE OFF)
if(NATIVE)
    if(MSVC)
        add_compile_options(-arch:AVX)
    else()
        add_compile_options(-mtune=native -march=native)
    endif()
elseif(NOT MSVC)
    add_compile_options(-mtune=generic)
endif()

add_subdirectory(lib/intx)
add_subdirectory(test)

write_basic_package_version_file(intxConfigVersion.cmake COMPATIBILITY ExactVersion)

set(config_dir ${CMAKE_INSTALL_LIBDIR}/cmake/intx)

configure_package_config_file(
    cmake/Config.cmake.in
    intxConfig.cmake
    INSTALL_DESTINATION ${config_dir}
)

install(
    EXPORT intxTargets
    NAMESPACE intx::
    DESTINATION ${config_dir}
)

install(
    FILES
    ${CMAKE_CURRENT_BINARY_DIR}/intxConfig.cmake
    ${CMAKE_CURRENT_BINARY_DIR}/intxConfigVersion.cmake
    DESTINATION ${config_dir}
)

if(WIN32)
    set(CPACK_GENERATOR ZIP)
else()
    set(CPACK_GENERATOR TGZ)
endif()
string(TOLOWER ${CMAKE_SYSTEM_NAME} system_name)
set(CPACK_PACKAGE_FILE_NAME ${PROJECT_NAME}-${PROJECT_VERSION}-${system_name})
set(CPACK_PACKAGE_CHECKSUM SHA256)
set(CPACK_INCLUDE_TOPLEVEL_DIRECTORY FALSE)
include(CPack)
