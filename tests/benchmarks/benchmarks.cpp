// Copyright 2017 Pawel Bylica.
// Governed by the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>
#include <intx/gmp.hpp>
#include <div.h>
#include <benchmark/benchmark.h>
#include <random>

using namespace intx;

using seed_type = std::random_device::result_type;

template<typename Int>
struct lcg
{
    Int state = 0;

    explicit lcg(seed_type seed) : state(seed)
    {
        // Run for some time to fill the state.
        for (int i = 0; i < 97; ++i)
            (*this)();
    }

    Int operator()()
    {
        state = static_cast<Int>(6364136223846793005 * state + 1442695040888963407);
        return state;
    }
};



static seed_type get_seed()
{
    static const auto seed = std::random_device{}();
    return seed;
}

template<uint64_t DivFn(uint64_t, uint64_t)>
static void soft_div64(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    std::mt19937_64 rng{get_seed()};
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
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udiv_qr);
BENCHMARK_TEMPLATE(udiv, uint128, uint128, udiv_qr_unr);

// Single digit divisor:
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint32_t, gmp_udiv_qr);

// Small divisor:
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint64_t, gmp_udiv_qr);

BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint128, gmp_udiv_qr);

BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_unr);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_shift);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_hd_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_llvm_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt_base);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, udiv_qr_knuth_opt);
BENCHMARK_TEMPLATE(udiv, uint256, uint256, gmp_udiv_qr);

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

BENCHMARK_TEMPLATE(binary_op256, (binary_fn256)&mul);
BENCHMARK_TEMPLATE(binary_op256, gmp_mul);

BENCHMARK_MAIN();