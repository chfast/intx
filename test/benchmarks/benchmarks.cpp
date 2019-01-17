// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../utils/gmp.hpp"
#include "../utils/random.hpp"

#include <benchmark/benchmark.h>
#include <div.hpp>
#include <intx/intx.hpp>

using namespace intx;

div_result<uint128> udivrem_by_ref(const uint128& x, const uint128& y) noexcept
{
    return udivrem(x, y);
}

template <typename N, typename D, div_result<N> DivFn(const N&, const N&)>
static void udiv(benchmark::State& state)
{
    // Pick random operands using global seed to perform exactly the same sequence of divisions
    // for each division implementation.
    lcg<seed_type> rng_seed(get_seed());
    lcg<N> rng_x(rng_seed());
    lcg<D> rng_y(rng_seed());

    constexpr size_t size = 1000;
    std::vector<N> input_x(size);
    std::vector<N> input_y(size);
    std::vector<div_result<N>> output(size);
    for (size_t i = 0; i < size; ++i)
    {
        // Generate non-zero divisor.
        do
            input_y[i] = rng_y();
        while (input_y[i] == 0);

        // Generate dividend greater than divisor to avoid trivial cases.
        do
            input_x[i] = rng_x();
        while (input_x[i] <= input_y[i]);
    }

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = DivFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }

    for (size_t i = 0; i < size; ++i)
    {
        auto x = output[i].quot * input_y[i] + output[i].rem;
        if (input_x[i] != x)
        {
            std::string error = to_string(input_x[i]) + " / " + to_string(input_y[i]) + " = " +
                                to_string(output[i].quot) + " % " + to_string(output[i].rem);
            state.SkipWithError(error.data());
            break;
        }
    }
}

BENCHMARK_TEMPLATE(udiv, uint128, uint64_t, udivrem_by_ref);
BENCHMARK_TEMPLATE(udiv, uint128, uint64_t, udivrem_unr);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udivrem_by_ref);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udivrem_unr);

BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udivrem_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udivrem);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, gmp::udivrem);

BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udivrem_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udivrem);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, gmp::udivrem);

BENCHMARK_TEMPLATE(udiv, uint256, uint128, udivrem_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udivrem);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, gmp::udivrem);

BENCHMARK_TEMPLATE(udiv, uint256, uint256, udivrem_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udivrem);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, gmp::udivrem);

BENCHMARK_TEMPLATE(udiv, uint512, uint32_t, udiv_qr_knuth_512);
BENCHMARK_TEMPLATE(udiv, uint512, uint32_t, udiv_qr_knuth_512_64);
BENCHMARK_TEMPLATE(udiv, uint512, uint32_t, udivrem);
BENCHMARK_TEMPLATE(udiv, uint512, uint32_t, gmp::udivrem);
BENCHMARK_TEMPLATE(udiv, uint512, uint64_t, udiv_qr_knuth_512);
BENCHMARK_TEMPLATE(udiv, uint512, uint64_t, udiv_qr_knuth_512_64);
BENCHMARK_TEMPLATE(udiv, uint512, uint64_t, udivrem);
BENCHMARK_TEMPLATE(udiv, uint512, uint64_t, gmp::udivrem);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, udiv_qr_knuth_512);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, udiv_qr_knuth_512_64);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, udivrem);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, gmp::udivrem);

using binary_fn256 = uint256 (*)(const uint256&, const uint256&);
template <binary_fn256 BinFn>
static void binary_op256(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    lcg<uint256> rng(get_seed());

    constexpr size_t size = 1000;
    std::vector<uint256> input_x(size);
    std::vector<uint256> input_y(size);
    std::vector<uint256> output(size);
    for (auto& x : input_x)
        x = rng();
    for (auto& y : input_y)
        y = rng();

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = BinFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }
}

BENCHMARK_TEMPLATE(binary_op256, mul);
BENCHMARK_TEMPLATE(binary_op256, mul_loop);
BENCHMARK_TEMPLATE(binary_op256, mul_loop_opt);
BENCHMARK_TEMPLATE(binary_op256, gmp::mul);

using binary_fn256_full = uint512 (*)(const uint256&, const uint256&);
template <binary_fn256_full BinFn>
static void binary_op256_full(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    lcg<uint256> rng(get_seed());

    constexpr size_t size = 1000;
    std::vector<uint256> input_x(size);
    std::vector<uint256> input_y(size);
    std::vector<uint512> output(size);
    for (auto& x : input_x)
        x = rng();
    for (auto& y : input_y)
        y = rng();

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = BinFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }
}

BENCHMARK_TEMPLATE(binary_op256_full, umul_full<uint256>);
BENCHMARK_TEMPLATE(binary_op256_full, umul_full_loop);
BENCHMARK_TEMPLATE(binary_op256_full, gmp::mul_full);

using binary_fn512 = uint512 (*)(const uint512&, const uint512&);
template <binary_fn512 BinFn>
static void binary_op512(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    lcg<uint512> rng(get_seed());

    constexpr size_t size = 1000;
    std::vector<uint512> input_x(size);
    std::vector<uint512> input_y(size);
    std::vector<uint512> output(size);
    for (auto& x : input_x)
        x = rng();
    for (auto& y : input_y)
        y = rng();

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = BinFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }
}

BENCHMARK_TEMPLATE(binary_op512, mul<uint512>);
BENCHMARK_TEMPLATE(binary_op512, gmp::mul);

template <typename Int, Int ShiftFn(Int, unsigned)>
static void shift(benchmark::State& state)
{
    lcg<Int> rng_x(get_seed());

    std::mt19937_64 rng{get_seed()};
    std::uniform_int_distribution<unsigned> dist_y(0, traits<Int>::bits);

    constexpr size_t size = 1000;
    std::vector<Int> input_x(size);
    std::vector<unsigned> input_y(size);
    std::vector<Int> output(size);
    for (auto& x : input_x)
        x = rng_x();
    for (auto& y : input_y)
        y = dist_y(rng);

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            output[i] = ShiftFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output.data());
    }
}
BENCHMARK_TEMPLATE(shift, uint256, shl);
BENCHMARK_TEMPLATE(shift, uint256, shl_loop);
BENCHMARK_TEMPLATE(shift, uint512, shl);
BENCHMARK_TEMPLATE(shift, uint512, shl_loop);
// BENCHMARK_TEMPLATE(shift_512, lsr);

static void count_sigificant_words32_256_loop(benchmark::State& state)
{
    auto s = static_cast<unsigned>(state.range(0));
    auto x = s != 0 ? uint256(0xff) << (s * 32 - 17) : uint256(0);
    benchmark::DoNotOptimize(x);

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        auto w = count_significant_words_loop<uint32_t>(x);
        benchmark::DoNotOptimize(w);
    }
}
BENCHMARK(count_sigificant_words32_256_loop)->DenseRange(0, 8);

static void count_sigificant_words32_256(benchmark::State& state)
{
    auto s = static_cast<unsigned>(state.range(0));
    auto x = s != 0 ? uint256(0xff) << (s * 32 - 17) : uint256(0);
    benchmark::DoNotOptimize(x);
    benchmark::ClobberMemory();

    for (auto _ : state)
    {
        benchmark::ClobberMemory();
        auto w = count_significant_words<uint32_t>(x);
        benchmark::DoNotOptimize(w);
    }
}
BENCHMARK(count_sigificant_words32_256)->DenseRange(0, 8);

BENCHMARK_MAIN();