# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

# Figure out if Hunter is needed.
if(INTX_TESTING OR INTX_BENCHMARKING)
    set(hunter_enabled TRUE)
else()
    set(hunter_enabled FALSE)
endif()

option(HUNTER_ENABLED "Enable Hunter package manager" ${hunter_enabled})

set(HUNTER_CONFIGURATION_TYPES Release CACHE STRING "Build type of the Hunter packages")
set(HUNTER_USE_CACHE_SERVERS NO CACHE STRING "Use Hunter cache servers")

file(
    DOWNLOAD https://raw.githubusercontent.com/cpp-pm/gate/v0.9.2/cmake/HunterGate.cmake
    ${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake
    EXPECTED_HASH SHA256=08d57ca550856c2f647c4863a25fa386e0d30e905e096a8eaeec336513b14ed1
)
include(${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake)

HunterGate(
    URL "https://github.com/cpp-pm/hunter/archive/v0.24.0.tar.gz"
    SHA1 "a3d7f4372b1dcd52faa6ff4a3bd5358e1d0e5efd"
    LOCAL
)
