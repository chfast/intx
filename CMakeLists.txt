# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

cmake_minimum_required(VERSION 3.5)

include(cmake/cable/bootstrap.cmake)

include(CableCompilerSettings)
include(CableToolchains)

cable_configure_toolchain(DEFAULT cxx14)

set(HUNTER_CONFIGURATION_TYPES Release
    CACHE STRING "Build type of the Hunter packages")
set(HUNTER_CACHE_SERVERS
    "https://github.com/ethereum/hunter-cache"
    CACHE STRING "Hunter cache servers")
include(HunterGate)
HunterGate(
    URL "https://github.com/ruslo/hunter/archive/v0.23.151.tar.gz"
    SHA1 "68657b81508c2d3c248731b5a0c2125f19866721"
)

project(intx)

option(INTX_TESTING "Build IntX with tests" ON)
option(INTX_FUZZING "Build intx fuzzers" OFF)

cable_configure_compiler(NO_PEDANTIC NO_CONVERSION_WARNINGS)

if(INTX_FUZZING)
    set(fuzzing_flags -fsanitize=fuzzer-no-link,undefined,address)
    add_compile_options(${fuzzing_flags})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${fuzzing_flags}")
endif()

option(NATIVE OFF)
if(NATIVE)
    add_compile_options(-mtune=native -march=native)
else()
    add_compile_options(-mtune=generic)
endif()

add_subdirectory(lib/intx)

if(INTX_TESTING)
    add_subdirectory(test)
endif()
