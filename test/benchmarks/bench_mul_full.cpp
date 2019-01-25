// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/mul_full.h>
#include <intx/int128.hpp>

#include "../utils/random.hpp"
#include <benchmark/benchmark.h>

template <typename RetT, RetT (*MulFn)(uint64_t, uint64_t)>
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
            auto p = MulFn(inputs[i], inputs[i + 1]);
            alo ^= p.lo;
            ahi ^= p.hi;
        }
        benchmark::DoNotOptimize(alo);
        benchmark::DoNotOptimize(ahi);
    }
}
BENCHMARK_TEMPLATE(mul_full, mul_full_64_result, mul_full_64_generic);
BENCHMARK_TEMPLATE(mul_full, mul_full_64_result, mul_full_64_native);
BENCHMARK_TEMPLATE(mul_full, intx::uint128, intx::umul_generic);
BENCHMARK_TEMPLATE(mul_full, intx::uint128, intx::umul);
