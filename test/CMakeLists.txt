# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_subdirectory(benchmarks)
add_subdirectory(integration)
add_subdirectory(unittests)

if(INTX_FUZZING)
    add_subdirectory(fuzzer)
endif()
