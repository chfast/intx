// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include "../utils/random.hpp"
#include <benchmark/benchmark.h>

using namespace intx;

std::tuple<uint512, uint32_t> udivrem_1_32_stable(const uint512& x, uint32_t y) noexcept;
std::tuple<uint512, uint32_t> udivrem_1_32_unr(const uint512& x, uint32_t y) noexcept;

std::tuple<uint512, uint64_t> udivrem_1_64(const uint512& u, uint64_t v) noexcept;
std::tuple<uint512, uint64_t> udivrem_1_64_unr(const uint512& u, uint64_t v) noexcept;

template<typename DivisorT, std::tuple<uint512, DivisorT> DivFn(const uint512&, DivisorT)>
static void udivrem_1(benchmark::State& state)
{
    lcg<uint512> rng512(get_seed());
    lcg<DivisorT> rng(get_seed());

    const auto x = rng512();
    const auto y = rng();

    uint512 q;
    DivisorT r = 0;

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        std::tie(q, r) = DivFn(x, y);
    }

    uint512 eq;
    uint64_t er = 1;
    std::tie(eq, er) = udivrem_1_64(x, y);
    if (q != eq || r != er)
        state.SkipWithError("incorrect division result");
}
BENCHMARK_TEMPLATE(udivrem_1, uint32_t, udivrem_1_32_stable);
BENCHMARK_TEMPLATE(udivrem_1, uint32_t, udivrem_1_32_unr);

BENCHMARK_TEMPLATE(udivrem_1, uint64_t, udivrem_1_64);
BENCHMARK_TEMPLATE(udivrem_1, uint64_t, udivrem_1_64_unr);
