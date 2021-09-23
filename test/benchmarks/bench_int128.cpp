// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <benchmark/benchmark.h>
#include <intx/intx.hpp>
#include <test/utils/gmp.hpp>
#include <test/utils/random.hpp>

using namespace intx;

uint128 div_gcc(uint128 x, uint128 y) noexcept;
inline div_result<uint128> gcc_(uint128 x, uint128 y) noexcept
{
    return {div_gcc(x, y), 0};
}

inline div_result<uint128> gmp_(uint128 x, uint128 y) noexcept
{
    return gmp::udivrem(x, y);
}

[[gnu::noinline]] static auto intx_(uint128 x, uint128 y) noexcept
{
    return intx::udivrem(x, y);
}

template <decltype(intx_) DivFn>
static void udiv128(benchmark::State& state)
{
    const uint128 inputs[][2] = {
        {0x537e3fbc5318dbc0e7e47d96b32ef2d5_u128, 0x395df916dfd1b5e38ae7c47ce8a620f_u128},
        {0x837e3fbc5318dbc0e7e47d96b32ef2d5_u128, 0x895df916dfd1b5e38ae7c47ce8a620f_u128},
        {0xee657725ff64cd48b8fe188a09dc4f78_u128, 3},                   // worst shift
        {0x0e657725ff64cd48b8fe188a09dc4f78_u128, 0xe7e47d96b32ef2d5},  // single long normalized
        {0x0e657725ff64cd48b8fe188a09dc4f78_u128, 0x77e47d96b32ef2d5},  // single long
    };
    benchmark::DoNotOptimize(inputs);
    benchmark::ClobberMemory();

    const auto idx = static_cast<size_t>(state.range(0));
    const uint128 x = inputs[idx][0];
    const uint128 y = inputs[idx][1];
    benchmark::DoNotOptimize(x);
    benchmark::DoNotOptimize(y);

    for ([[maybe_unused]] auto _ : state)
    {
        auto q = DivFn(x, y);
        benchmark::DoNotOptimize(q);
    }
}
BENCHMARK_TEMPLATE(udiv128, gcc_)->DenseRange(0, 3);
BENCHMARK_TEMPLATE(udiv128, intx_)->DenseRange(0, 3);
BENCHMARK_TEMPLATE(udiv128, gmp_)->DenseRange(0, 3);


template <typename RetT, RetT (*MulFn)(uint64_t, uint64_t)>
static void umul128(benchmark::State& state)
{
    const auto inputs = test::gen_uniform_seq(1000);
    benchmark::ClobberMemory();

    while (state.KeepRunningBatch(inputs.size()))
    {
        uint64_t alo = 0;
        uint64_t ahi = 0;
        for (size_t i = 0; i < inputs.size() - 1; ++i)
        {
            auto p = MulFn(inputs[i], inputs[i + 1]);
            alo ^= p[0];
            ahi ^= p[1];
        }
        benchmark::DoNotOptimize(alo);
        benchmark::DoNotOptimize(ahi);
    }
}
BENCHMARK_TEMPLATE(umul128, intx::uint128, intx::umul);
