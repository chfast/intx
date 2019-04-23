# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

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
