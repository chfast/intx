# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_compile_options(
    $<$<CXX_COMPILER_ID:MSVC>:-wd5030>  # allow unknown attributes
)

add_subdirectory(analysis)
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
