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

std::tuple<uint512, uint64_t> udivrem_1_64_recint(const uint512& u, uint64_t v) noexcept;
std::tuple<uint512, uint512> udivrem_recint(const uint512& u, const uint512& v) noexcept;
std::tuple<uint512, uint256> udivrem_recint(const uint512& u, const uint256& v) noexcept;
std::tuple<uint512, uint128> udivrem_recint(const uint512& u, const uint128& v) noexcept;

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
    DivisorT er = 1;
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
BENCHMARK_TEMPLATE(udivrem_1, uint512, uint64_t, udivrem_1_64_recint);

template <typename DividendT, typename DivisorT,
    std::tuple<DividendT, DivisorT> DivFn(const DividendT&, const DivisorT&)>
static void udivrem(benchmark::State& state)
{
    lcg<DividendT> rng_x(get_seed());
    lcg<DivisorT> rng_y(get_seed());

    const auto x = rng_x();
    const auto y = rng_y();

    DividendT q;
    DivisorT r{};

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        std::tie(q, r) = DivFn(x, y);
    }

    DividendT eq;
    DivisorT er;
    std::tie(eq, er) = udivrem_gmp(x, y);
    if (q != eq || r != er)
        state.SkipWithError("incorrect division result");
}
BENCHMARK_TEMPLATE(udivrem, uint512, uint128, udivrem_gmp);
BENCHMARK_TEMPLATE(udivrem, uint512, uint128, udivrem_recint);
BENCHMARK_TEMPLATE(udivrem, uint512, uint256, udivrem_gmp);
BENCHMARK_TEMPLATE(udivrem, uint512, uint256, udivrem_recint);
BENCHMARK_TEMPLATE(udivrem, uint512, uint512, udivrem_gmp);
BENCHMARK_TEMPLATE(udivrem, uint512, uint512, udivrem_recint);


std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_llvm2(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept;
std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_llvm3(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept;
std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_hd2(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept;
std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_hd3(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept;

template<decltype(udivrem_knuth_normalize_32_llvm2) Fn>
static void udivrem_knuth_normalize(benchmark::State& state)
{
    lcg<uint32_t> rng(get_seed());

    uint32_t u[16];
    uint32_t v[16];

    size_t n = 3;

    for (auto& w : u)
        w = rng();

    for (size_t i = 0; i < n; ++i)
        v[i] = rng();

    while (v[n - 1] == 0 || (v[n - 1] & 0x80000000))
        v[n - 1] = rng();

    for (auto _ : state)
        Fn(u, v, n);
}
BENCHMARK_TEMPLATE(udivrem_knuth_normalize, udivrem_knuth_normalize_32_llvm2);
BENCHMARK_TEMPLATE(udivrem_knuth_normalize, udivrem_knuth_normalize_32_llvm3);
BENCHMARK_TEMPLATE(udivrem_knuth_normalize, udivrem_knuth_normalize_32_hd2);
BENCHMARK_TEMPLATE(udivrem_knuth_normalize, udivrem_knuth_normalize_32_hd3);
