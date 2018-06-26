// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <div.h>
#include <intx/intx.hpp>

#include "../utils/gmp.hpp"
#include "../utils/random.hpp"
#include <benchmark/benchmark.h>

using namespace intx;

template<uint64_t DivFn(uint64_t, uint64_t)>
static void udivrem_64(benchmark::State& state)
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

    for (size_t i = 0; i < size; ++i)
    {
        if (output[i] != input_x[i] / input_y[i])
        {
            state.SkipWithError("wrong result");
            break;
        }
    }
}

static uint64_t div(uint64_t x, uint64_t y) { return x / y; }

BENCHMARK_TEMPLATE(udivrem_64, div);
BENCHMARK_TEMPLATE(udivrem_64, soft_div_shift);
BENCHMARK_TEMPLATE(udivrem_64, soft_div_improved_shift);
BENCHMARK_TEMPLATE(udivrem_64, soft_div_unr);
BENCHMARK_TEMPLATE(udivrem_64, soft_div_unr_unrolled);

template<std::tuple<uint64_t, uint64_t> DivFn(unsigned __int128, uint64_t)>
static void udivrem_long_64(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    std::mt19937_64 rng{get_seed()};
    std::uniform_int_distribution<uint64_t> dist_x;
    std::uniform_int_distribution<uint64_t> dist_y(1);

    constexpr size_t size = 1000;
    std::vector<unsigned __int128> input_x(size);
    std::vector<uint64_t> input_y(size);
    std::vector<uint64_t> output_q(size);
    std::vector<uint64_t> output_r(size);

    for (size_t i = 0; i < size; ++i)
    {
        // Find input pairs without division overflow.
        unsigned __int128 q;
        unsigned __int128 x;
        uint64_t y;
        do
        {
            x = (unsigned __int128)dist_x(rng) * dist_x(rng) + dist_x(rng);
            y = dist_y(rng);
            q = x / y;
        } while (q > std::numeric_limits<uint64_t>::max());

        input_x[i] = x;
        input_y[i] = y;
    }

    for (auto _ : state)
    {
        for (size_t i = 0; i < size; ++i)
            std::tie(output_q[i], output_r[i]) = DivFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output_q.data());
        benchmark::DoNotOptimize(output_r.data());
    }

    for (size_t i = 0; i < size; ++i)
    {
        auto x = input_x[i];
        auto y = input_y[i];
        auto q = output_q[i];
//        auto r = output_r[i];

        auto expected_q = x / y;

        if (q != expected_q)
        {
            state.SkipWithError("wrong q");
            break;
        }
    }
}
BENCHMARK_TEMPLATE(udivrem_long_64, udivrem_long_gcc);
BENCHMARK_TEMPLATE(udivrem_long_64, udivrem_long_rt);
BENCHMARK_TEMPLATE(udivrem_long_64, gcc::udivrem_long);


template<typename N, typename D, std::tuple<N, N> DivFn(N, N)>
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
    std::vector<N> output_q(size);
    std::vector<N> output_r(size);
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
            std::tie(output_q[i], output_r[i]) = DivFn(input_x[i], input_y[i]);
        benchmark::DoNotOptimize(output_q.data());
        benchmark::DoNotOptimize(output_r.data());
    }

    for (size_t i = 0; i < size; ++i)
    {
        auto x = output_q[i] * input_y[i] + output_r[i];
        if (input_x[i] != x)
        {
            std::string error = to_string(input_x[i]) + " / " + to_string(input_y[i]) + " = " +
                                to_string(output_q[i]) + " % " + to_string(output_r[i]);
            state.SkipWithError(error.data());
            break;
        }
    }
}

BENCHMARK_TEMPLATE(udiv, uint128, uint64_t, udiv_qr);
BENCHMARK_TEMPLATE(udiv, uint128, uint64_t, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint128, uint64_t, udiv_dc);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udiv_qr);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udiv_dc);

// Single digit divisor:
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_dc);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, gmp_udiv_qr);

// Small divisor:
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_dc);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, gmp_udiv_qr);

BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_dc);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, gmp_udiv_qr);

BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_dc);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_64);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, gmp_udiv_qr);

//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_qr_unr);
//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_dc);
//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_qr_shift);
//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_qr_knuth_hd_base);
//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_qr_knuth_llvm_base);
//BENCHMARK_TEMPLATE(udiv, uint512, uint512, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, udiv_qr_knuth_512);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, udiv_qr_knuth_512_64);
BENCHMARK_TEMPLATE(udiv, uint512, uint256, gmp_udiv_qr);

using binary_fn256 = uint256 (*)(uint256, uint256);
template<binary_fn256 BinFn>
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
BENCHMARK_TEMPLATE(binary_op256, gmp_mul);

using binary_fn256_full = uint512 (*)(uint256, uint256);
template<binary_fn256_full BinFn>
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
BENCHMARK_TEMPLATE(binary_op256_full, gmp_mul_full);

using binary_fn512 = uint512 (*)(uint512, uint512);
template<binary_fn512 BinFn>
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

BENCHMARK_TEMPLATE(binary_op512, mul512);
BENCHMARK_TEMPLATE(binary_op512, gmp_mul);

template<typename Int, Int ShiftFn(Int, unsigned)>
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
//BENCHMARK_TEMPLATE(shift_512, lsr);

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