# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

set(HUNTER_CONFIGURATION_TYPES Release CACHE STRING "Build type of the Hunter packages")
set(HUNTER_USE_CACHE_SERVERS NO CACHE STRING "Use Hunter cache servers")

file(
    DOWNLOAD https://raw.githubusercontent.com/cpp-pm/gate/v0.11.0/cmake/HunterGate.cmake
    ${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake
    EXPECTED_HASH SHA256=ad0f10e9d759826b1b564df833d7db743c34ed60515499b77f5e98f9d09d355a
)
include(${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake)

HunterGate(
    URL "https://github.com/cpp-pm/hunter/archive/v0.26.12.tar.gz"
    SHA1 "6498c5d0dec25d7fffb2b0574ebaf265179b894d"
)
