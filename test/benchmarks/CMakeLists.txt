# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

add_executable(intx-bench
    bench_div.cpp
    bench_int128.cpp
    bench_mul_full.cpp
    benchmarks.cpp
    div.h
    utils.cpp
)
target_link_libraries(intx-bench PRIVATE intx benchmark::benchmark GMP::gmp)
set_target_properties(intx-bench PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
