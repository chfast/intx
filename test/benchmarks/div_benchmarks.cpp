// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include "gmp_wrappers.hpp"
#include "../utils/random.hpp"
#include <benchmark/benchmark.h>

using namespace intx;

std::tuple<uint256, uint32_t> udivrem_1_32_long(const uint256& x, uint32_t y) noexcept;
std::tuple<uint256, uint32_t> udivrem_1_32_unr(const uint256& x, uint32_t y) noexcept;

std::tuple<uint512, uint32_t> udivrem_1_32_long(const uint512& x, uint32_t y) noexcept;
std::tuple<uint512, uint32_t> udivrem_1_32_unr(const uint512& x, uint32_t y) noexcept;

std::tuple<uint512, uint64_t> udivrem_1_64_long(const uint512& u, uint64_t v) noexcept;
std::tuple<uint512, uint64_t> udivrem_1_64_unr(const uint512& u, uint64_t v) noexcept;

template <typename DividendT, typename DivisorT,
    std::tuple<DividendT, DivisorT> DivFn(const DividendT&, DivisorT)>
static void udivrem_1(benchmark::State& state)
{
    lcg<DividendT> rng_x(get_seed());
    lcg<DivisorT> rng_y(get_seed());

    const auto x = rng_x();
    const auto y = rng_y();

    DividendT q;
    DivisorT r = 0;

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        std::tie(q, r) = DivFn(x, y);
    }

    DividendT eq;
    uint64_t er = 1;
    std::tie(eq, er) = udivrem_1_64_gmp(x, y);
    if (q != eq || r != er)
        state.SkipWithError("incorrect division result");
}
BENCHMARK_TEMPLATE(udivrem_1, uint256, uint32_t, udivrem_1_32_long);
BENCHMARK_TEMPLATE(udivrem_1, uint256, uint32_t, udivrem_1_32_unr);

BENCHMARK_TEMPLATE(udivrem_1, uint512, uint32_t, udivrem_1_32_long);
BENCHMARK_TEMPLATE(udivrem_1, uint512, uint32_t, udivrem_1_32_unr);

BENCHMARK_TEMPLATE(udivrem_1, uint512, uint64_t, udivrem_1_64_long);
BENCHMARK_TEMPLATE(udivrem_1, uint512, uint64_t, udivrem_1_64_unr);
BENCHMARK_TEMPLATE(udivrem_1, uint512, uint64_t, udivrem_1_64_gmp);
