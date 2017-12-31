// Copyright 2017 Pawel Bylica.
// Governed by the Apache License, Version 2.0. See the LICENSE file.

#include <div.h>
#include <intx.hpp>
#include <gmp.h>
#include <benchmark/benchmark.h>
#include <random>

template<typename Int>
struct lcg
{
    Int state = 0;

    explicit lcg(std::random_device::result_type seed) : state(seed)
    {
        // Run for some time to fill the state.
        for (int i = 0; i < 17; ++i)
            (*this)();
    }

    Int operator()()
    {
        state = 6364136223846793005 * state + 1442695040888963407;
        return state;
    }
};

template<uint64_t DivFn(uint64_t, uint64_t)>
static void soft_div64(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    std::mt19937_64 rng{std::random_device{}()};
    std::uniform_int_distribution<uint64_t> dist_x;
    std::uniform_int_distribution<uint64_t> dist_y(1, 100);

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

    for (size_t i = 0; i < size; ++i)
    {
        if (output[i] != input_x[i] / input_y[i])
            state.SkipWithError("wrong result");
    }
}

static uint64_t div(uint64_t x, uint64_t y) { return x / y; }

BENCHMARK_TEMPLATE(soft_div64, div);
BENCHMARK_TEMPLATE(soft_div64, soft_div_shift);
BENCHMARK_TEMPLATE(soft_div64, soft_div_improved_shift);
BENCHMARK_TEMPLATE(soft_div64, soft_div_unr);
BENCHMARK_TEMPLATE(soft_div64, soft_div_unr_unrolled);

static std::tuple<intx::uint256, intx::uint256> gmp_udiv_qr(intx::uint256 x, intx::uint256 y)
{
    using namespace intx;
    // Skip dividend's leading zero limbs.
    static constexpr size_t limbs = sizeof(uint256) / sizeof(mp_limb_t);
    const size_t y_limbs = limbs - (clz(y) / (sizeof(mp_limb_t) * 8));

    uint256 q, r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_tdiv_qr(p_q, p_r, 0, p_x, limbs, p_y, y_limbs);
    return {q, r};
};

template<std::tuple<intx::uint256, intx::uint256> DivFn(intx::uint256, intx::uint256)>
static void udiv256(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    auto seed = std::random_device{}();
    std::mt19937_64 rng{seed};
    lcg<intx::uint256> rng_x(seed);
    std::uniform_int_distribution<uint64_t> dist_y(1);

    constexpr size_t size = 1000;
    std::vector<intx::uint256> input_x(size);
    std::vector<intx::uint256> input_y(size);
    std::vector<intx::uint256> output_q(size);
    std::vector<intx::uint256> output_r(size);
    for (auto& x : input_x)
        x = rng_x();
    for (auto& y : input_y)
        y = dist_y(rng);

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            std::tie(output_q[i], output_r[i]) = DivFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output_q.data());
        benchmark::DoNotOptimize(output_r.data());
    }

    for (size_t i = 0; i < size; ++i)
    {
        intx::uint256 x = output_q[i] * input_y[i] + output_r[i];
        if (input_x[i] != x)
            state.SkipWithError("wrong result");
    }
}

BENCHMARK_TEMPLATE(udiv256, intx::udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv256, gmp_udiv_qr);

BENCHMARK_MAIN();