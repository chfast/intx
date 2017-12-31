add_executable(
    bench
    benchmarks.cpp
)

target_link_libraries(bench PRIVATE intx benchmark::benchmark GMP::gmp)
target_compile_options(bench PRIVATE -fno-omit-frame-pointer)
target_compile_options(bench PRIVATE -march=native -mtune=native)