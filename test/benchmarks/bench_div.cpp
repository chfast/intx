// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include "../utils/random.hpp"

#include <div.hpp>
#include <experiments.hpp>

#include <benchmark/benchmark.h>

uint64_t udiv_native(uint64_t x, uint64_t y) noexcept;
uint64_t nop(uint64_t x, uint64_t y) noexcept;
uint64_t soft_div_unr_unrolled(uint64_t x, uint64_t y) noexcept;
uint64_t soft_div_unr(uint64_t x, uint64_t y) noexcept;

using namespace intx;

template <decltype(div::normalize) NormalizeFn>
static void div_normalize(benchmark::State& state)
{
    uint512 u{uint256{1324254353, 4343242153453}, uint256{100324254353, 48882153453}};
    uint512 v{uint256{1333354353, 4343242156663}, uint256{16666654353, 48882100453}};

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        auto x = NormalizeFn(u, v);
        benchmark::DoNotOptimize(x);
    }
}
BENCHMARK_TEMPLATE(div_normalize, div::normalize);

constexpr uint64_t neg(uint64_t x) noexcept
{
    return ~x;
}

template <decltype(experiments::reciprocal) Fn>
static void div_unary(benchmark::State& state)
{
    auto input = gen_uniform_seq(1000);
    for (auto& i : input)
        i |= (uint64_t{1} << 63);

    benchmark::ClobberMemory();
    for (auto _ : state)
    {
        for (auto& i : input)
            i = Fn(i);
    }
    benchmark::DoNotOptimize(input.data());
}
BENCHMARK_TEMPLATE(div_unary, neg);
BENCHMARK_TEMPLATE(div_unary, experiments::reciprocal);

template <uint64_t DivFn(uint64_t, uint64_t)>
static void udiv64(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    std::mt19937_64 rng{get_seed()};
    std::uniform_int_distribution<uint64_t> dist_x;
    std::uniform_int_distribution<uint64_t> dist_y(1, 200);

    constexpr size_t size = 1000;
    std::vector<uint64_t> input_x(size);
    std::vector<uint64_t> input_y(size);
    std::vector<uint64_t> output(size);
    for (auto& x : input_x)
        x = dist_x(rng);
    for (auto& y : input_y)
        y = dist_y(rng);

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = DivFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }

    if (DivFn == nop)
        return;

    // Check results.
    for (size_t i = 0; i < size; ++i)
    {
        if (output[i] != input_x[i] / input_y[i])
        {
            state.SkipWithError("wrong result");
            break;
        }
    }
}


BENCHMARK_TEMPLATE(udiv64, nop);
BENCHMARK_TEMPLATE(udiv64, experiments::udiv_by_reciprocal);
BENCHMARK_TEMPLATE(udiv64, udiv_native);
BENCHMARK_TEMPLATE(udiv64, soft_div_unr);
BENCHMARK_TEMPLATE(udiv64, soft_div_unr_unrolled);
