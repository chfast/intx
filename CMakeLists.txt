# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

cmake_minimum_required(VERSION 3.5)

include(cmake/cable/bootstrap.cmake)

include(CableToolchains)

cable_configure_toolchain(DEFAULT cxx14)

set(HUNTER_CONFIGURATION_TYPES Release
    CACHE STRING "Build type of the Hunter packages")
set(HUNTER_CACHE_SERVERS
    "https://github.com/ethereum/hunter-cache"
    CACHE STRING "Hunter cache servers")
include(HunterGate)
HunterGate(
    URL "https://github.com/ruslo/hunter/archive/v0.19.167.tar.gz"
    SHA1 "244a13718ea2e6c0c8998d15559c7e459f615708"
)

project(intx)

option(INTX_TESTING "Build IntX with tests" ON)
option(INTX_FUZZING "Build intx fuzzers" OFF)

if(INTX_FUZZING)
    set(fuzzing_flags -fsanitize=fuzzer-no-link,undefined,address)
    add_compile_options(${fuzzing_flags})
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${fuzzing_flags}")
endif()

# FIXME: Add back -Wconversion, test with clang.
add_compile_options(-Werror -Wall -Wextra)
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-omit-frame-pointer -fsanitize=address")

option(NATIVE OFF)
if(NATIVE)
    add_compile_options(-mtune=native -march=native)
else()
    add_compile_options(-mtune=generic)
endif()

#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Og")
#set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -Og")

add_subdirectory(lib/intx)

if(INTX_TESTING)
    add_subdirectory(test)
endif()
