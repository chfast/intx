# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

hunter_add_package(benchmark)
find_package(benchmark CONFIG REQUIRED)

find_package(GMP REQUIRED)

add_executable(intx-bench
    ../experimental/addmod.hpp
    bench_builtins.cpp
    bench_div.cpp
    bench_int128.cpp
    benchmarks.cpp
    noinline.cpp
    utils.cpp
)
target_link_libraries(intx-bench PRIVATE intx intx::experimental intx::testutils benchmark::benchmark GMP::gmp)
set_target_properties(intx-bench PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
