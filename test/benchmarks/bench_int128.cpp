// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

#include <benchmark/benchmark.h>

using namespace intx;

uint128 div_gcc(uint128 x, uint128 y) noexcept;

inline uint128 div_uint128(uint128 x, uint128 y) noexcept
{
    return x / y;
}

template <decltype(div_gcc) DivFn>
static void udiv128(benchmark::State& state)
{
    uint128 x = {0x537e3fbc5318dbc0, 0xe7e47d96b32ef2d5};
    uint128 y = {0x395df916dfd1b5e, 0x38ae7c47ce8a620f};

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        auto q = DivFn(x, y);
        benchmark::DoNotOptimize(q);
    }
}
BENCHMARK_TEMPLATE(udiv128, div_gcc);
BENCHMARK_TEMPLATE(udiv128, div_uint128);


template <decltype(div_gcc) DivFn>
static void udiv128_worst_shift(benchmark::State& state)
{
    uint128 x = {0xee657725ff64cd48, 0xb8fe188a09dc4f78};
    uint128 y = 3;

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        auto q = DivFn(x, y);
        benchmark::DoNotOptimize(q);
    }
}
BENCHMARK_TEMPLATE(udiv128_worst_shift, div_gcc);
BENCHMARK_TEMPLATE(udiv128_worst_shift, div_uint128);
