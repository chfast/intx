# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

set(HUNTER_CONFIGURATION_TYPES Release CACHE STRING "Build type of the Hunter packages")
set(HUNTER_USE_CACHE_SERVERS NO CACHE STRING "Use Hunter cache servers")

file(
    DOWNLOAD https://raw.githubusercontent.com/cpp-pm/gate/v0.10.0/cmake/HunterGate.cmake
    ${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake
    EXPECTED_HASH SHA256=3da4dcd5dca35679d6c822c0ac23b7b91d86d481f838bad4baca88410b4bde72
)
include(${INTX_DEPS_DOWNLOAD_DIR}/HunterGate.cmake)

HunterGate(
    URL "https://github.com/cpp-pm/hunter/archive/v0.25.6.tar.gz"
    SHA1 "69e4a05bd514bb05cb2c5aa02ce8ac420516aaf7"
)
