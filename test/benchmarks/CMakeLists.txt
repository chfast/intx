# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

add_executable(intx-bench benchmarks.cpp)
target_link_libraries(intx-bench PRIVATE intx benchmark::benchmark GMP::gmp)
target_compile_options(intx-bench PRIVATE -fno-omit-frame-pointer)
target_compile_options(intx-bench PRIVATE -march=native -mtune=native)
set_target_properties(intx-bench PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
