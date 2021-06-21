# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

# Figure out if Hunter is needed.
if(INTX_TESTING OR INTX_BENCHMARKING)
    set(hunter_enabled TRUE)
else()
    set(hunter_enabled FALSE)
endif()

option(HUNTER_ENABLED "Enable Hunter package manager" ${hunter_enabled})

set(HUNTER_CONFIGURATION_TYPES Release
    CACHE STRING "Build type of the Hunter packages")
set(HUNTER_CACHE_SERVERS
    "https://github.com/ethereum/hunter-cache"
    CACHE STRING "Hunter cache servers")

file(
    DOWNLOAD https://raw.githubusercontent.com/cpp-pm/gate/v0.9.2/cmake/HunterGate.cmake
    ${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake
    EXPECTED_HASH SHA256=08d57ca550856c2f647c4863a25fa386e0d30e905e096a8eaeec336513b14ed1
)
include(${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake)

HunterGate(
    URL "https://github.com/cpp-pm/hunter/archive/v0.23.246.tar.gz"
    SHA1 "b28940a87bba9c3f40182692d6fdaf1c9d735840"
    LOCAL
)
