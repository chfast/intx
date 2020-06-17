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

include(HunterGate)

HunterGate(
    URL https://github.com/cpp-pm/hunter/archive/v0.23.239.tar.gz
    SHA1 135567a8493ab3499187bce1f2a8df9b449febf3
)
