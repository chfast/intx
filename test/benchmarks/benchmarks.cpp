// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <benchmark/benchmark.h>
#include <experimental/add.hpp>
#include <intx/intx.hpp>
#include <test/utils/gmp.hpp>
#include <test/utils/random.hpp>

using namespace intx;
using namespace intx::test;


template <typename ArgT, div_result<ArgT> DivFn(const ArgT&, const ArgT&)>
static void div(benchmark::State& state) noexcept
{
    const auto divison_set_id = [&state]() noexcept {
        switch (state.range(0))
        {
        case 64:
            return x_64;
        case 128:
            return x_128;
        case 192:
            return x_192;
        case 256:
            return lt_256;
        default:
            state.SkipWithError("unexpected argument");
            return x_64;
        }
    }();

    const auto& xs = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? x_256 : x_512);
    const auto& ys = test::get_samples<ArgT>(divison_set_id);

    while (state.KeepRunningBatch(xs.size()))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            const auto _ = DivFn(xs[i], ys[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(div, uint256, udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint256, gmp::udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint512, udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint512, gmp::udivrem)->DenseRange(64, 256, 64);


template <uint256 ModFn(const uint256&, const uint256&, const uint256&)>
static void mod(benchmark::State& state)
{
    const auto mod_set_id = [&state]() noexcept {
        switch (state.range(0))
        {
        case 64:
            return x_64;
        case 128:
            return x_128;
        case 192:
            return x_192;
        case 256:
            return lt_256;
        default:
            state.SkipWithError("unexpected argument");
            return x_64;
        }
    }();

    const auto& xs = test::get_samples<uint256>(x_256);
    const auto& ys = test::get_samples<uint256>(y_256);
    const auto& ms = test::get_samples<uint256>(mod_set_id);

    while (state.KeepRunningBatch(xs.size()))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            const auto _ = ModFn(xs[i], ys[i], ms[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(mod, addmod)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(mod, mulmod)->DenseRange(64, 256, 64);


inline auto public_mul(const uint256& x, const uint256& y) noexcept
{
    return x * y;
}

inline uint256 mul_loop(const uint256& u, const uint256& v) noexcept
{
    return umul_loop(u, v).lo;
}

inline auto inline_add(const uint256& x, const uint256& y) noexcept
{
    return x + y;
}

uint256 add(const uint256& x, const uint256& y) noexcept;

inline auto inline_sub(const uint256& x, const uint256& y) noexcept
{
    return x - y;
}

uint256 sub(const uint256& x, const uint256& y) noexcept;

uint256 exp(const uint256& x, const uint256& y) noexcept;

inline auto inline_add(const uint512& x, const uint512& y) noexcept
{
    return x + y;
}

uint512 add(const uint512& x, const uint512& y) noexcept;

inline auto inline_sub(const uint512& x, const uint512& y) noexcept
{
    return x - y;
}

uint512 sub(const uint512& x, const uint512& y) noexcept;

inline auto public_mul(const uint512& x, const uint512& y) noexcept
{
    return x * y;
}

template <typename ResultT, typename ArgT, ResultT BinOp(const ArgT&, const ArgT&)>
static void binop(benchmark::State& state)
{
    const auto& xs = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? x_256 : x_512);
    const auto& ys = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? y_256 : y_512);

    while (state.KeepRunningBatch(xs.size()))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            const auto _ = BinOp(xs[i], ys[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(binop, uint256, uint256, add);
BENCHMARK_TEMPLATE(binop, uint256, uint256, inline_add);
BENCHMARK_TEMPLATE(binop, uint256, uint256, sub);
BENCHMARK_TEMPLATE(binop, uint256, uint256, inline_sub);
BENCHMARK_TEMPLATE(binop, uint256, uint256, experimental::add_recursive);
BENCHMARK_TEMPLATE(binop, uint256, uint256, experimental::add_waterflow);
BENCHMARK_TEMPLATE(binop, uint256, uint256, mul);
BENCHMARK_TEMPLATE(binop, uint256, uint256, mul_loop);
BENCHMARK_TEMPLATE(binop, uint256, uint256, mul_loop_opt);
BENCHMARK_TEMPLATE(binop, uint256, uint256, public_mul);
BENCHMARK_TEMPLATE(binop, uint256, uint256, gmp::mul);

BENCHMARK_TEMPLATE(binop, uint512, uint256, umul);
BENCHMARK_TEMPLATE(binop, uint512, uint256, umul_loop);
BENCHMARK_TEMPLATE(binop, uint512, uint256, gmp::mul_full);

BENCHMARK_TEMPLATE(binop, uint512, uint512, add);
BENCHMARK_TEMPLATE(binop, uint512, uint512, inline_add);
BENCHMARK_TEMPLATE(binop, uint512, uint512, sub);
BENCHMARK_TEMPLATE(binop, uint512, uint512, inline_sub);
BENCHMARK_TEMPLATE(binop, uint512, uint512, mul);
BENCHMARK_TEMPLATE(binop, uint512, uint512, public_mul);
BENCHMARK_TEMPLATE(binop, uint512, uint512, gmp::mul);

template <unsigned N>
inline intx::uint<N> shl(const intx::uint<N>& x, unsigned y) noexcept
{
    return x << y;
}

template <typename Int, Int ShiftFn(const Int&, unsigned)>
static void shift(benchmark::State& state)
{
    const auto& xs = test::get_samples<Int>(sizeof(Int) == sizeof(uint256) ? x_256 : x_512);

    while (state.KeepRunningBatch(xs.size()))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            const auto x = xs[i];
            const auto sh = static_cast<unsigned>(x) & (Int::num_bits - 1);
            const auto _ = ShiftFn(x, sh);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(shift, uint256, shl);
BENCHMARK_TEMPLATE(shift, uint256, shl_loop);
BENCHMARK_TEMPLATE(shift, uint512, shl);
BENCHMARK_TEMPLATE(shift, uint512, shl_loop);
// BENCHMARK_TEMPLATE(shift_512, lsr);

static void exponentiation(benchmark::State& state)
{
    const auto exponent_set_id = [&state]() noexcept {
        switch (state.range(0))
        {
        case 64:
            return x_64;
        case 128:
            return x_128;
        case 192:
            return x_192;
        case 256:
            return x_256;
        default:
            state.SkipWithError("unexpected argument");
            return x_64;
        }
    }();

    const auto& bs = test::get_samples<uint256>(x_256);
    const auto& es = test::get_samples<uint256>(exponent_set_id);

    while (state.KeepRunningBatch(bs.size()))
    {
        for (size_t i = 0; i < bs.size(); ++i)
        {
            const auto _ = exp(bs[i], es[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK(exponentiation)->DenseRange(64, 256, 64);

static void exponentiation2(benchmark::State& state)
{
    const auto base = uint256{2};
    const auto exponent = static_cast<unsigned>(state.range(0));

    for (auto _ : state)
    {
        const auto e = exp(base, exponent);
        benchmark::DoNotOptimize(e);
    }
}
BENCHMARK(exponentiation2)->Arg(0)->RangeMultiplier(2)->Range(64, 512);

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

template <typename Int>
static void to_string(benchmark::State& state)
{
    // Pick random operands. Keep the divisor small, because this is the worst
    // case for most algorithms.
    lcg<Int> rng(get_seed());

    constexpr size_t size = 1000;
    std::vector<Int> input(size);
    for (auto& x : input)
        x = rng();

    while (state.KeepRunningBatch(size))
    {
        for (size_t i = 0; i < size; ++i)
        {
            auto s = intx::to_string(input[i]);
            benchmark::DoNotOptimize(s.data());
        }
    }
}
BENCHMARK_TEMPLATE(to_string, uint128);
BENCHMARK_TEMPLATE(to_string, uint256);
BENCHMARK_TEMPLATE(to_string, uint512);

BENCHMARK_MAIN();
