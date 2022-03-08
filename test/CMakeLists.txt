# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

if(CMAKE_VERSION VERSION_GREATER_EQUAL 3.12)
    add_subdirectory(analysis)
endif()

add_subdirectory(experimental)
add_subdirectory(utils)
add_subdirectory(integration)
add_subdirectory(unittests)

if(INTX_BENCHMARKING)
    add_subdirectory(benchmarks)
endif()

if(INTX_FUZZING)
    add_subdirectory(fuzzer)
endif()
