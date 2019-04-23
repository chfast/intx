# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

cmake_minimum_required(VERSION 3.5)

include(cmake/cable/bootstrap.cmake)

include(CableCompilerSettings)
include(CableToolchains)

cable_configure_toolchain(DEFAULT cxx14)

include(Hunter/init)

project(intx)

option(INTX_TESTING "Build intx with tests" ON)
option(INTX_BENCHMARKING "Build intx with benchmark tools" ON)
option(INTX_FUZZING "Build intx fuzzers" OFF)

cable_configure_compiler(NO_PEDANTIC NO_CONVERSION_WARNINGS)

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

if(INTX_TESTING OR INTX_BENCHMARKING OR INTX_FUZZING)
    add_subdirectory(test)
endif()
