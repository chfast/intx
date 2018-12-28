// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include "../utils/random.hpp"

#include <div.hpp>
#include <experiments.hpp>

#include <benchmark/benchmark.h>

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