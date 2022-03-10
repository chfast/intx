// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <benchmark/benchmark.h>
#include <intx/intx.hpp>
#include <test/utils/random.hpp>

uint64_t udiv_native(uint64_t x, uint64_t y) noexcept;
uint64_t nop(uint64_t x, uint64_t y) noexcept;
uint64_t soft_div_unr_unrolled(uint64_t x, uint64_t y) noexcept;
uint64_t soft_div_unr(uint64_t x, uint64_t y) noexcept;

uint64_t reciprocal_2by1_noinline(uint64_t d) noexcept;
uint64_t reciprocal_3by2_noinline(intx::uint128 d) noexcept;

using namespace intx;

inline uint64_t udiv_by_reciprocal(uint64_t uu, uint64_t du) noexcept
{
    auto shift = __builtin_clzl(du);
    auto u = uint128{uu} << shift;
    auto d = du << shift;
    auto v = reciprocal_2by1(d);

    return udivrem_2by1(u, d, v).quot;
}


template <decltype(internal::normalize<512, 512>) NormalizeFn>
static void div_normalize(benchmark::State& state)
{
    auto u = uint512{1324254353, 0, 4343242153453, 0, 100324254353, 0, 48882153453, 0};
    auto v = uint512{1333354353, 0, 4343242156663, 0, 16666654353, 0, 48882100453, 0};

    for ([[maybe_unused]] auto _ : state)
    {
        benchmark::ClobberMemory();
        auto x = NormalizeFn(u, v);
        benchmark::DoNotOptimize(x);
    }
}
BENCHMARK_TEMPLATE(div_normalize, internal::normalize);

constexpr uint64_t neg(uint64_t x) noexcept
{
    return ~x;
}

inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    const auto u = uint128{~uint64_t{0}, ~d};
    uint64_t v{};

#if __x86_64__
    uint64_t _{};
    asm("divq %4" : "=d"(_), "=a"(v) : "d"(u[1]), "a"(u[0]), "g"(d));  // NOLINT(hicpp-no-assembler)
#else
    v = (u / d)[0];
#endif

    return v;
}

template <typename T, uint64_t Fn(T)>
static void reciprocal(benchmark::State& state)
{
    auto samples = test::get_samples<T>(test::norm);

    benchmark::ClobberMemory();
    uint64_t x = 0;
    while (state.KeepRunningBatch(test::num_samples))
    {
        for (const auto& i : samples)
            x ^= Fn(i);
    }
    benchmark::DoNotOptimize(x);
}
BENCHMARK_TEMPLATE(reciprocal, uint64_t, neg);
BENCHMARK_TEMPLATE(reciprocal, uint64_t, reciprocal_naive);
BENCHMARK_TEMPLATE(reciprocal, uint64_t, reciprocal_2by1);
BENCHMARK_TEMPLATE(reciprocal, uint64_t, reciprocal_2by1_noinline);
BENCHMARK_TEMPLATE(reciprocal, uint128, reciprocal_3by2);
BENCHMARK_TEMPLATE(reciprocal, uint128, reciprocal_3by2_noinline);

template <uint64_t DivFn(uint64_t, uint64_t)>
static void udiv64(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    std::mt19937_64 rng{test::get_seed()};
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

    while (state.KeepRunningBatch(size))
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
BENCHMARK_TEMPLATE(udiv64, udiv_by_reciprocal);
BENCHMARK_TEMPLATE(udiv64, udiv_native);
BENCHMARK_TEMPLATE(udiv64, soft_div_unr);
BENCHMARK_TEMPLATE(udiv64, soft_div_unr_unrolled);
