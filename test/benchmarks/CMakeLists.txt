# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

set(givaro_dir /home/chfast/Projects/ethereum/givaro)
set(recint_dir ${givaro_dir}/src/kernel/recint)
#file(GLOB recint_sources ${recint_dir}/*.h)
#add_library(recint ${recint_sources})
#target_include_directories(recint PUBLIC ${recint_dir})

add_executable(intx-bench
    bench_mul_full.cpp
    benchmarks.cpp
    div_benchmarks.cpp
    div_implementations.cpp
    div_knuth_implementations.cpp
    gmp_wrappers.hpp
    recint_wrappers.cpp
)
target_link_libraries(intx-bench PRIVATE intx benchmark::benchmark GMP::gmp)
set_target_properties(intx-bench PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
target_include_directories(intx-bench PRIVATE ${givaro_dir} ${recint_dir})
