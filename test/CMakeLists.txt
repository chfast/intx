# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

set(intx_internal_include_dir ${PROJECT_SOURCE_DIR}/lib)

add_subdirectory(utils)

if(INTX_TESTING OR INTX_BENCHMARKING)
    add_subdirectory(experimental)
endif()

if(INTX_TESTING)
    add_subdirectory(integration)
    add_subdirectory(unittests)
endif()

if(INTX_BENCHMARKING)
    add_subdirectory(benchmarks)
endif()

if(INTX_FUZZING)
    add_subdirectory(fuzzer)
endif()
