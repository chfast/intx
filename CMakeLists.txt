# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

cmake_minimum_required(VERSION 3.10)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

include(CableCompilerSettings)
include(CMakeDependentOption)

set(INTX_DEPS_DOWNLOAD_DIR ${CMAKE_CURRENT_SOURCE_DIR}/deps/download)

get_directory_property(has_parent PARENT_DIRECTORY)
if(NOT has_parent)
    set(is_main_project TRUE)
endif()

option(INTX_INSTALL "Enable intx install target" ${is_main_project})

option(INTX_TESTING "Enable intx testing" ${is_main_project})
cmake_dependent_option(INTX_BENCHMARKING "Build intx with benchmark tools" ON "INTX_TESTING" OFF)
cmake_dependent_option(INTX_FUZZING "Build intx fuzzers" OFF "INTX_TESTING" OFF)

if(INTX_TESTING)
    include(Hunter/init)
endif()

project(intx LANGUAGES CXX)
set(PROJECT_VERSION 0.8.0)

cable_configure_compiler(NO_STACK_PROTECTION)

if(INTX_FUZZING)
    set(fuzzing_flags -fsanitize=fuzzer-no-link,undefined,address)
    add_compile_options(${fuzzing_flags})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${fuzzing_flags}")
endif()


include(CMakePackageConfigHelpers)
include(GNUInstallDirs)
set(INTX_INCLUDE_DIR ${PROJECT_SOURCE_DIR}/include)

add_library(intx INTERFACE)
add_library(intx::intx ALIAS intx)
target_compile_features(intx INTERFACE cxx_std_17)
target_sources(intx INTERFACE $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}/intx/intx.hpp>)
target_include_directories(intx INTERFACE $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}>$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)


if(INTX_TESTING)
    enable_testing()
    add_subdirectory(test)
endif()

if(INTX_INSTALL)
    write_basic_package_version_file(intxConfigVersion.cmake COMPATIBILITY ExactVersion)

    set(config_dir ${CMAKE_INSTALL_LIBDIR}/cmake/intx)

    configure_package_config_file(
        cmake/Config.cmake.in
        intxConfig.cmake
        INSTALL_DESTINATION ${config_dir}
    )

    install(
        TARGETS intx
        EXPORT intxTargets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
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

    install(
        DIRECTORY
        ${INTX_INCLUDE_DIR}/
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    )

    if(WIN32)
        set(CPACK_GENERATOR ZIP)
    else()
        set(CPACK_GENERATOR TGZ)
    endif()
    set(CPACK_PACKAGE_FILE_NAME ${PROJECT_NAME}-${PROJECT_VERSION})
    set(CPACK_PACKAGE_CHECKSUM SHA256)
    set(CPACK_INCLUDE_TOPLEVEL_DIRECTORY FALSE)
    include(CPack)
endif()
