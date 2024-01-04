// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../experimental/addmod.hpp"
#include <benchmark/benchmark.h>
#include <intx/intx.hpp>
#include <test/utils/gmp.hpp>
#include <test/utils/random.hpp>

#if __clang_major__ >= 11 && __clang_major__ <= 13 && !defined(__apple_build_version__)
    #define INTX_HAS_EXTINT 1
#else
    #define INTX_HAS_EXTINT 0
#endif

using namespace intx;
using namespace intx::test;

// TODO: Move them here with [[gnu::noinline]]
uint256 add(const uint256& x, const uint256& y) noexcept;
uint512 add(const uint512& x, const uint512& y) noexcept;
uint256 sub(const uint256& x, const uint256& y) noexcept;
uint512 sub(const uint512& x, const uint512& y) noexcept;
uint256 exp(const uint256& x, const uint256& y) noexcept;

namespace
{
template <typename ArgT, div_result<ArgT> DivFn(const ArgT&, const ArgT&)>
void div(benchmark::State& state) noexcept
{
    const auto division_set_id = [&state]() noexcept {
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
    const auto& ys = test::get_samples<ArgT>(division_set_id);

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = DivFn(xs[i], ys[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(div, uint256, udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint256, gmp::udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint512, udivrem)->DenseRange(64, 256, 64);
BENCHMARK_TEMPLATE(div, uint512, gmp::udivrem)->DenseRange(64, 256, 64);


template <uint256 ModFn(const uint256&, const uint256&, const uint256&)>
void mod(benchmark::State& state)
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

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = ModFn(xs[i], ys[i], ms[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
#define ARGS DenseRange(64, 256, 64)
BENCHMARK_TEMPLATE(mod, addmod)->ARGS;
BENCHMARK_TEMPLATE(mod, addmod_public)->ARGS;
BENCHMARK_TEMPLATE(mod, addmod_simple)->ARGS;
BENCHMARK_TEMPLATE(mod, addmod_prenormalize)->ARGS;
BENCHMARK_TEMPLATE(mod, addmod_daosvik_v1)->ARGS;
BENCHMARK_TEMPLATE(mod, addmod_daosvik_v2)->ARGS;
BENCHMARK_TEMPLATE(mod, mulmod)->ARGS;
#undef ARGS

template <uint256 ModFn(const uint256&, const uint256&, const uint256&)>
void ecmod(benchmark::State& state)
{
    // Samples such x <= m, y <= m.
    const auto& xs = test::get_samples<uint256>(lt_x_256);
    const auto& ys = test::get_samples<uint256>(lt_256);
    const auto& ms = test::get_samples<uint256>(x_256);

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = ModFn(xs[i], ys[i], ms[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(ecmod, addmod_public);
BENCHMARK_TEMPLATE(ecmod, addmod_simple);
BENCHMARK_TEMPLATE(ecmod, addmod_prenormalize);
BENCHMARK_TEMPLATE(ecmod, addmod_daosvik_v1);
BENCHMARK_TEMPLATE(ecmod, addmod_daosvik_v2);
BENCHMARK_TEMPLATE(ecmod, mulmod);


template <unsigned N>
[[gnu::noinline]] auto public_mul(const intx::uint<N>& x, const intx::uint<N>& y) noexcept
{
    return x * y;
}

template <unsigned N>
[[gnu::noinline]] auto umul_(const intx::uint<N>& x, const intx::uint<N>& y) noexcept
{
    return intx::umul(x, y);
}

inline auto inline_add(const uint256& x, const uint256& y) noexcept
{
    return x + y;
}

inline auto inline_sub(const uint256& x, const uint256& y) noexcept
{
    return x - y;
}


inline auto inline_add(const uint512& x, const uint512& y) noexcept
{
    return x + y;
}


inline auto inline_sub(const uint512& x, const uint512& y) noexcept
{
    return x - y;
}


template <typename ResultT, typename ArgT, ResultT BinOp(const ArgT&, const ArgT&)>
void binop(benchmark::State& state)
{
    const auto& xs = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? x_256 : x_512);
    const auto& ys = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? y_256 : y_512);

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = BinOp(xs[i], ys[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(binop, uint256, uint256, add);
BENCHMARK_TEMPLATE(binop, uint256, uint256, inline_add);
BENCHMARK_TEMPLATE(binop, uint256, uint256, sub);
BENCHMARK_TEMPLATE(binop, uint256, uint256, inline_sub);
BENCHMARK_TEMPLATE(binop, uint256, uint256, public_mul);
BENCHMARK_TEMPLATE(binop, uint256, uint256, gmp::mul);

BENCHMARK_TEMPLATE(binop, uint512, uint256, umul_);
BENCHMARK_TEMPLATE(binop, uint512, uint256, gmp::mul_full);

BENCHMARK_TEMPLATE(binop, uint512, uint512, add);
BENCHMARK_TEMPLATE(binop, uint512, uint512, inline_add);
BENCHMARK_TEMPLATE(binop, uint512, uint512, sub);
BENCHMARK_TEMPLATE(binop, uint512, uint512, inline_sub);
BENCHMARK_TEMPLATE(binop, uint512, uint512, public_mul);
BENCHMARK_TEMPLATE(binop, uint512, uint512, gmp::mul);

template <unsigned N>
[[gnu::noinline]] intx::uint<N> shl_public(const intx::uint<N>& x, const uint64_t& y) noexcept
{
    return x << y;
}

template <unsigned N>
[[gnu::noinline]] intx::uint<N> shl_public(const intx::uint<N>& x, const intx::uint<N>& y) noexcept
{
    return x << y;
}

[[gnu::noinline]] intx::uint256 shl_halves(const intx::uint256& x, const uint64_t& shift) noexcept
{
    constexpr auto num_bits = 256;
    constexpr auto half_bits = num_bits / 2;

    const auto xlo = uint128{x[0], x[1]};

    if (shift < half_bits)
    {
        const auto lo = xlo << shift;

        const auto xhi = uint128{x[2], x[3]};

        // Find the part moved from lo to hi.
        // The shift right here can be invalid:
        // for shift == 0 => lshift == half_bits.
        // Split it into 2 valid shifts by (rshift - 1) and 1.
        const auto rshift = half_bits - shift;
        const auto lo_overflow = (xlo >> (rshift - 1)) >> 1;
        const auto hi = (xhi << shift) | lo_overflow;
        return {lo[0], lo[1], hi[0], hi[1]};
    }

    // This check is only needed if we want "defined" behavior for shifts
    // larger than size of the Int.
    if (shift < num_bits)
    {
        const auto hi = xlo << (shift - half_bits);
        return {0, 0, hi[0], hi[1]};
    }

    return 0;
}

[[gnu::noinline]] intx::uint256 shl_halves(
    const intx::uint256& x, const uint256& big_shift) noexcept
{
    if (INTX_UNLIKELY((big_shift[3] | big_shift[2] | big_shift[1]) != 0))
        return 0;

    const auto shift = big_shift[0];


    constexpr auto num_bits = 256;
    constexpr auto half_bits = num_bits / 2;

    const auto xlo = uint128{x[0], x[1]};

    if (shift < half_bits)
    {
        const auto lo = xlo << shift;

        const auto xhi = uint128{x[2], x[3]};

        // Find the part moved from lo to hi.
        // The shift right here can be invalid:
        // for shift == 0 => lshift == half_bits.
        // Split it into 2 valid shifts by (rshift - 1) and 1.
        const auto rshift = half_bits - shift;
        const auto lo_overflow = (xlo >> (rshift - 1)) >> 1;
        const auto hi = (xhi << shift) | lo_overflow;
        return {lo[0], lo[1], hi[0], hi[1]};
    }

    // This check is only needed if we want "defined" behavior for shifts
    // larger than size of the Int.
    if (shift < num_bits)
    {
        const auto hi = xlo << (shift - half_bits);
        return {0, 0, hi[0], hi[1]};
    }

    return 0;
}

#if INTX_HAS_EXTINT
[[gnu::noinline]] static intx::uint256 shl_llvm(const intx::uint256& x, const uint64_t& y) noexcept
{
    unsigned _ExtInt(256) a;  // NOLINT(cppcoreguidelines-init-variables)
    std::memcpy(&a, &x, sizeof(a));
    const auto b = a << y;
    uint256 r;
    std::memcpy(&r, &b, sizeof(r));
    return r;
}
#endif


template <typename ArgT, typename ShiftT, ArgT ShiftFn(const ArgT&, const ShiftT&)>
void shift(benchmark::State& state)
{
    const auto& shift_samples_id = [&state]() noexcept {
        switch (state.range(0))
        {
        case -1:
            return shift_mixed;
        case 0:
            return shift_w0;
        case 1:
            return shift_w1;
        case 2:
            return shift_w2;
        case 3:
            return shift_w3;
        default:
            state.SkipWithError("unexpected argument");
            return shift_mixed;
        }
    }();

    const auto& xs = test::get_samples<ArgT>(sizeof(ArgT) == sizeof(uint256) ? x_256 : x_512);
    const auto& raw_shifts = test::get_samples<uint64_t>(shift_samples_id);
    std::array<ShiftT, test::num_samples> shifts{};
    std::copy(std::cbegin(raw_shifts), std::cend(raw_shifts), std::begin(shifts));

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = ShiftFn(xs[i], shifts[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(shift, uint256, uint256, shl_public)->DenseRange(-1, 3);
BENCHMARK_TEMPLATE(shift, uint256, uint256, shl_halves)->DenseRange(-1, 3);
BENCHMARK_TEMPLATE(shift, uint256, uint64_t, shl_public)->DenseRange(-1, 3);
BENCHMARK_TEMPLATE(shift, uint256, uint64_t, shl_halves)->DenseRange(-1, 3);
#if INTX_HAS_EXTINT
BENCHMARK_TEMPLATE(shift, uint256, uint64_t, shl_llvm)->DenseRange(-1, 3);
#endif
BENCHMARK_TEMPLATE(shift, uint512, uint512, shl_public)->DenseRange(-1, 3);
BENCHMARK_TEMPLATE(shift, uint512, uint64_t, shl_public)->DenseRange(-1, 3);

[[gnu::noinline]] bool lt_public(const uint256& x, const uint256& y) noexcept
{
    return x < y;
}

[[gnu::noinline]] bool lt_sub(const uint256& x, const uint256& y) noexcept
{
    return subc(x, y).carry;
}

[[gnu::noinline]] bool lt_split(const uint256& x, const uint256& y) noexcept
{
    auto xp = uint128{x[2], x[3]};
    auto yp = uint128{y[2], y[3]};
    if (xp == yp)
    {
        xp = uint128{x[0], x[1]};
        yp = uint128{y[0], y[1]};
    }
    return xp < yp;
}

[[gnu::noinline]] bool lt_wordcmp(const uint256& x, const uint256& y) noexcept
{
    for (size_t i = 3; i >= 1; --i)
    {
        if (x[i] < y[i])
            return true;
        if (x[i] > y[i])
            return false;
    }
    return x[0] < y[0];
}

/// Find the first different word and compares it.
/// Proposed in https://github.com/chfast/intx/pull/269.
[[gnu::noinline]] bool lt_ne(const uint256& x, const uint256& y) noexcept
{
    for (auto i = uint256::num_words - 1; i > 0; --i)
    {
        if (x[i] != y[i])
            return x[i] < y[i];
    }
    return x[0] < y[0];
}

/// A modification of lt_ne(). Smaller code, saves one cmp instruction.
[[gnu::noinline]] bool lt_ne2(const uint256& x, const uint256& y) noexcept
{
    auto a = x[3];
    auto b = y[3];
    for (auto i = uint256::num_words - 1; i > 0;)
    {
        if (a != b)
            break;
        --i;
        a = x[i];
        b = y[i];
    }
    return a < b;
}

[[gnu::noinline]] bool lt_halves(const uint256& x, const uint256& y) noexcept
{
    const auto xhi = uint128{x[2], x[3]};
    const auto xlo = uint128{x[0], x[1]};
    const auto yhi = uint128{y[2], y[3]};
    const auto ylo = uint128{y[0], y[1]};
    return int{xhi < yhi} | (int{xhi == yhi} & int{xlo < ylo});
}

#if INTX_HAS_EXTINT
[[gnu::noinline]] bool lt_llvm(const uint256& x, const uint256& y) noexcept
{
    unsigned _ExtInt(256) a;  // NOLINT(cppcoreguidelines-init-variables)
    unsigned _ExtInt(256) b;  // NOLINT(cppcoreguidelines-init-variables)
    std::memcpy(&a, &x, sizeof(a));
    std::memcpy(&b, &y, sizeof(b));
    return a < b;
}
#endif

template <bool CmpFn(const uint256&, const uint256&)>
void compare(benchmark::State& state)
{
    const auto [x_id, y_id] = [&state]() noexcept -> std::pair<samples_set_id, samples_set_id> {
        switch (state.range(0))
        {
        case 0:
            return {x_256_mixed, y_256_mixed};
        case 64:
            return {x_64, y_64};
        case 128:
            return {x_128, y_128};
        case 192:
            return {x_192, y_192};
        case 256:
            return {x_256, y_256};
        default:
            state.SkipWithError("unexpected argument");
            return {};
        }
    }();

    const auto& xs = test::get_samples<uint256>(x_id);
    const auto& ys = test::get_samples<uint256>(y_id);

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(xs.size())))
    {
        for (size_t i = 0; i < xs.size(); ++i)
        {
            auto _ = CmpFn(xs[i], ys[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK_TEMPLATE(compare, lt_public)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_sub)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_split)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_wordcmp)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_ne)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_ne2)->DenseRange(0, 256, 64);
BENCHMARK_TEMPLATE(compare, lt_halves)->DenseRange(0, 256, 64);
#if INTX_HAS_EXTINT
BENCHMARK_TEMPLATE(compare, lt_llvm)->DenseRange(0, 256, 64);
#endif

void exponentiation(benchmark::State& state)
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

    while (state.KeepRunningBatch(static_cast<benchmark::IterationCount>(bs.size())))
    {
        for (size_t i = 0; i < bs.size(); ++i)
        {
            auto _ = exp(bs[i], es[i]);
            benchmark::DoNotOptimize(_);
        }
    }
}
BENCHMARK(exponentiation)->DenseRange(64, 256, 64);

void exponentiation2(benchmark::State& state)
{
    const auto base = uint256{2};
    const auto exponent = static_cast<unsigned>(state.range(0));

    for ([[maybe_unused]] auto _ : state)
    {
        auto e = exp(base, exponent);
        benchmark::DoNotOptimize(e);
    }
}
BENCHMARK(exponentiation2)->Arg(0)->RangeMultiplier(2)->Range(64, 512);

void count_sigificant_words_256(benchmark::State& state)
{
    auto s = static_cast<unsigned>(state.range(0));
    auto x = s != 0 ? uint256(0xff) << (s * 32 - 17) : uint256(0);
    benchmark::DoNotOptimize(x);
    benchmark::ClobberMemory();

    for ([[maybe_unused]] auto _ : state)
    {
        benchmark::ClobberMemory();
        auto w = count_significant_words(x);
        benchmark::DoNotOptimize(w);
    }
}
BENCHMARK(count_sigificant_words_256)->DenseRange(0, 8);

template <typename Int>
void to_string(benchmark::State& state)
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


template <typename Int>
[[gnu::noinline]] auto load_be(const uint8_t* data) noexcept
{
    return intx::be::unsafe::load<Int>(data);
}

template <typename Int>
[[gnu::noinline]] auto store_be(uint8_t* data, const Int& v) noexcept
{
    intx::be::unsafe::store(data, v);
}

template <typename Int>
void load_store_be(benchmark::State& state)
{
    uint8_t load_buffer[sizeof(Int) + 7]{};
    const auto unaligned_load_ptr = load_buffer + 7;
    uint8_t store_buffer[sizeof(Int) + 1]{};
    const auto unaligned_store_ptr = store_buffer + 1;

    for ([[maybe_unused]] auto _ : state)
    {
        auto v = load_be<Int>(unaligned_load_ptr);
        store_be(unaligned_store_ptr, v);
    }
}
BENCHMARK_TEMPLATE(load_store_be, uint128);
BENCHMARK_TEMPLATE(load_store_be, uint256);
BENCHMARK_TEMPLATE(load_store_be, uint512);
}  // namespace

BENCHMARK_MAIN();
