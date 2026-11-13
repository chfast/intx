// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <benchmark/benchmark.h>
#include <intx/intx.hpp>
#include <test/utils/gmp.hpp>
#include <test/utils/random.hpp>

using namespace intx;

namespace
{
#if INTX_HAS_BUILTIN_INT128
inline div_result<int128> gcc_(int128 x, int128 y) noexcept
{
    const auto bx = (static_cast<builtin_int128>(static_cast<int64_t>(x[1])) << 64) | x[0];
    const auto by = (static_cast<builtin_int128>(static_cast<int64_t>(y[1])) << 64) | y[0];
    return {int128{bx / by}, 0};
}
#endif

inline div_result<int128> gmp_(int128 x, int128 y) noexcept
{
    const auto x_is_neg = x < 0;
    const auto y_is_neg = y < 0;
    const auto x_abs = x_is_neg ? -x : x;
    const auto y_abs = y_is_neg ? -y : y;

    // Convert to uint128 to use gmp::udivrem
    const auto res = gmp::udivrem(uint128{x_abs[0], x_abs[1]}, uint128{y_abs[0], y_abs[1]});

    const auto q_is_neg = x_is_neg ^ y_is_neg;
    const int128 q{res.quot[0], res.quot[1]};
    const int128 r{res.rem[0], res.rem[1]};

    return {q_is_neg ? -q : q, x_is_neg ? -r : r};
}

[[gnu::noinline]] auto intx_(int128 x, int128 y) noexcept
{
    return div_result<int128>{x / y, x % y};
}

template <decltype(intx_) DivFn>
void sdiv128(benchmark::State& state)
{
    int128 inputs[][2] = {
        {{0x537e3fbc5318dbc0e7e47d96b32ef2d5_u128 [0], 0x537e3fbc5318dbc0e7e47d96b32ef2d5_u128 [1]},
            {0x395df916dfd1b5e38ae7c47ce8a620f_u128 [0],
                0x395df916dfd1b5e38ae7c47ce8a620f_u128 [1]}},
        {-int128{0x837e3fbc5318dbc0e7e47d96b32ef2d5_u128 [0],
             0x837e3fbc5318dbc0e7e47d96b32ef2d5_u128 [1]},
            {0x895df916dfd1b5e38ae7c47ce8a620f_u128 [0],
                0x895df916dfd1b5e38ae7c47ce8a620f_u128 [1]}},
        {{0xee657725ff64cd48b8fe188a09dc4f78_u128 [0], 0xee657725ff64cd48b8fe188a09dc4f78_u128 [1]},
            -3},  // worst shift
        {-int128{0x0e657725ff64cd48b8fe188a09dc4f78_u128 [0],
             0x0e657725ff64cd48b8fe188a09dc4f78_u128 [1]},
            {0xe7e47d96b32ef2d5}},  // single long normalized
        {{0x0e657725ff64cd48b8fe188a09dc4f78_u128 [0], 0x0e657725ff64cd48b8fe188a09dc4f78_u128 [1]},
            -int128{0x77e47d96b32ef2d5}},  // single long
    };
    benchmark::DoNotOptimize(inputs);
    benchmark::ClobberMemory();

    const auto idx = static_cast<size_t>(state.range(0));
    int128 x = inputs[idx][0];
    int128 y = inputs[idx][1];
    benchmark::DoNotOptimize(x);
    benchmark::DoNotOptimize(y);

    for ([[maybe_unused]] auto _ : state)
    {
        auto q = DivFn(x, y);
        benchmark::DoNotOptimize(q);
    }
}
#if INTX_HAS_BUILTIN_INT128
BENCHMARK(sdiv128<gcc_>)->DenseRange(0, 4);
#endif
BENCHMARK(sdiv128<intx_>)->DenseRange(0, 4);
BENCHMARK(sdiv128<gmp_>)->DenseRange(0, 4);


template <typename RetT, RetT (*MulFn)(int64_t, int64_t)>
void smul128(benchmark::State& state)
{
    const auto inputs = test::gen_uniform_seq(1000);
    benchmark::ClobberMemory();

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(inputs.size())))
    {
        uint64_t alo = 0;
        uint64_t ahi = 0;
        for (size_t i = 0; i < inputs.size() - 1; ++i)
        {
            auto p = MulFn(static_cast<int64_t>(inputs[i]), static_cast<int64_t>(inputs[i + 1]));
            alo ^= p[0];
            ahi ^= p[1];
        }
        benchmark::DoNotOptimize(alo);
        benchmark::DoNotOptimize(ahi);
    }
}

inline int128 smul(int64_t x, int64_t y) noexcept
{
#if INTX_HAS_BUILTIN_INT128
    return int128{static_cast<builtin_int128>(x) * static_cast<builtin_int128>(y)};
#else
    return int128{x} * int128{y};
#endif
}

BENCHMARK(smul128<int128, smul>);
}  // namespace
