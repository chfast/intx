// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <mul_full.h>

#include "../utils/random.hpp"
#include <benchmark/benchmark.h>

template<decltype(mul_full_64) MulFn>
static void mul_full(benchmark::State& state)
{
    auto inputs = gen_uniform_seq(1000);
    benchmark::ClobberMemory();

    for (auto _ : state)
    {
        uint64_t alo = 0;
        uint64_t ahi = 0;
        for (size_t i = 0; i < inputs.size() - 1; ++i)
        {
            uint64_t hi;
            alo ^= MulFn(inputs[i], inputs[i + 1], &hi);
            ahi ^= hi;
        }
        benchmark::DoNotOptimize(alo);
        benchmark::DoNotOptimize(ahi);
    }
}
BENCHMARK_TEMPLATE(mul_full, mul_full_64_generic);
BENCHMARK_TEMPLATE(mul_full, mul_full_64_native);
