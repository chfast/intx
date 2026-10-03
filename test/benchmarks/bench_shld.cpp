// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

// Benchmarks of funnel shift implementations (SHLD/SHRD vs shift sequences) on x86-64.

#include <benchmark/benchmark.h>
#include <array>
#include <cstdint>
#include <random>
#include <vector>

namespace
{
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
    #define SHLD_BENCH_X86 1

/// SHLD/SHRD with the count in CL (handles shift 0).
struct shld_asm
{
    static uint64_t fshl(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        asm("shldq %%cl, %1, %0" : "+r"(hi) : "r"(lo), "c"(s) : "cc");
        return hi;
    }
    static uint64_t fshr(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        asm("shrdq %%cl, %1, %0" : "+r"(lo) : "r"(hi), "c"(s) : "cc");
        return lo;
    }
};

/// The LLVM "slow-shld" expansion: shl, shr 1, not, shr, or (handles shift 0).
struct shift5_asm
{
    static uint64_t fshl(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        uint64_t t;
        asm("shlq %%cl, %0\n\t"
            "movq %3, %1\n\t"
            "shrq $1, %1\n\t"
            "notb %%cl\n\t"
            "shrq %%cl, %1\n\t"
            "orq %1, %0"
            : "+r"(hi), "=&r"(t), "+c"(s)
            : "r"(lo)
            : "cc");
        return hi;
    }
    static uint64_t fshr(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        uint64_t t;
        asm("shrq %%cl, %0\n\t"
            "leaq (%3,%3), %1\n\t"
            "notb %%cl\n\t"
            "shlq %%cl, %1\n\t"
            "orq %1, %0"
            : "+r"(lo), "=&r"(t), "+c"(s)
            : "r"(hi)
            : "cc");
        return lo;
    }
};

/// shl, neg, shr, or and cmov for shift 0 (GCC's code for the zero-safe form).
struct cmov_asm
{
    static uint64_t fshl(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        uint64_t r, t;
        const unsigned s0 = s;
        asm("movq %3, %0\n\t"
            "shlq %%cl, %0\n\t"
            "movq %4, %1\n\t"
            "negb %%cl\n\t"
            "shrq %%cl, %1\n\t"
            "orq %1, %0\n\t"
            "testl %5, %5\n\t"
            "cmovzq %3, %0"
            : "=&r"(r), "=&r"(t), "+c"(s)
            : "r"(hi), "r"(lo), "r"(s0)
            : "cc");
        return r;
    }
    static uint64_t fshr(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        uint64_t r, t;
        const unsigned s0 = s;
        asm("movq %4, %0\n\t"
            "shrq %%cl, %0\n\t"
            "movq %3, %1\n\t"
            "negb %%cl\n\t"
            "shlq %%cl, %1\n\t"
            "orq %1, %0\n\t"
            "testl %5, %5\n\t"
            "cmovzq %4, %0"
            : "=&r"(r), "=&r"(t), "+c"(s)
            : "r"(hi), "r"(lo), "r"(s0)
            : "cc");
        return r;
    }
};

/// BMI2 shifts for word arrays with the shift == 0 case handled outside (see words_hoisted).
/// The fshl/fshr take the complementary count ns = 64 - s and require s != 0.
struct bmi2_asm
{
    static uint64_t fshl_nz(uint64_t hi, uint64_t lo, uint64_t s, uint64_t ns) noexcept
    {
        uint64_t r, t;
        asm("shlxq %3, %2, %0\n\t"
            "shrxq %5, %4, %1\n\t"
            "orq %1, %0"
            : "=&r"(r), "=&r"(t)
            : "r"(hi), "r"(s), "r"(lo), "r"(ns)
            : "cc");
        return r;
    }
    static uint64_t fshr_nz(uint64_t hi, uint64_t lo, uint64_t s, uint64_t ns) noexcept
    {
        uint64_t r, t;
        asm("shrxq %3, %2, %0\n\t"
            "shlxq %5, %4, %1\n\t"
            "orq %1, %0"
            : "=&r"(r), "=&r"(t)
            : "r"(lo), "r"(s), "r"(hi), "r"(ns)
            : "cc");
        return r;
    }
};
#endif

/// The C++ form compiled by the compiler (clang: SHLD/SHRD, GCC: shifts + cmov).
struct cxx
{
    static uint64_t fshl(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        return s == 0 ? hi : (hi << s) | (lo >> (64 - s));
    }
    static uint64_t fshr(uint64_t hi, uint64_t lo, unsigned s) noexcept
    {
        return s == 0 ? lo : (lo >> s) | (hi << (64 - s));
    }
};

/// The C++ form requiring s != 0, used with the shift == 0 case handled outside (words_hoisted).
struct cxx_nz
{
    static uint64_t fshl_nz(uint64_t hi, uint64_t lo, uint64_t s, uint64_t ns) noexcept
    {
        return (hi << s) | (lo >> ns);
    }
    static uint64_t fshr_nz(uint64_t hi, uint64_t lo, uint64_t s, uint64_t ns) noexcept
    {
        return (lo >> s) | (hi << ns);
    }
};

constexpr size_t num_inputs = 4096;

struct inputs
{
    std::vector<uint64_t> words;
    std::vector<unsigned> shifts;
};

/// Random words and shift counts. With zero = false the counts are in [1, 63], otherwise [0, 63].
const inputs& get_inputs(bool zero)
{
    static const auto make = [](bool z) {
        std::mt19937_64 rng{z ? 2u : 1u};
        inputs in;
        in.words.resize(num_inputs * 9);
        for (auto& w : in.words)
            w = rng();
        in.shifts.resize(num_inputs);
        for (auto& s : in.shifts)
            s = z ? static_cast<unsigned>(rng() % 64) : static_cast<unsigned>(rng() % 63 + 1);
        return in;
    };
    static const inputs nz = make(false);
    static const inputs wz = make(true);
    return zero ? wz : nz;
}

/// Latency: a dependent chain of funnel shifts. Arg: 0 = shifts [1,63], 1 = [0,63].
template <typename V, bool Left>
void fsh_lat(benchmark::State& state)
{
    const auto& in = get_inputs(state.range(0) != 0);
    uint64_t x = 1;
    for ([[maybe_unused]] auto _ : state)
    {
        for (size_t i = 0; i < num_inputs; ++i)
            x = Left ? V::fshl(x, in.words[i], in.shifts[i]) :
                       V::fshr(in.words[i], x, in.shifts[i]);
        benchmark::DoNotOptimize(x);
    }
    state.SetItemsProcessed(state.iterations() * static_cast<int64_t>(num_inputs));
}

/// Throughput: independent funnel shifts.
template <typename V, bool Left>
void fsh_tput(benchmark::State& state)
{
    const auto& in = get_inputs(state.range(0) != 0);
    std::vector<uint64_t> out(num_inputs);
    for ([[maybe_unused]] auto _ : state)
    {
        for (size_t i = 0; i < num_inputs; ++i)
        {
            const auto hi = in.words[2 * i];
            const auto lo = in.words[2 * i + 1];
            out[i] = Left ? V::fshl(hi, lo, in.shifts[i]) : V::fshr(hi, lo, in.shifts[i]);
        }
        benchmark::DoNotOptimize(out.data());
        benchmark::ClobberMemory();
    }
    state.SetItemsProcessed(state.iterations() * static_cast<int64_t>(num_inputs));
}

/// Word array shifts as in the division normalization (left) and denormalization (right).
template <typename V, size_t W>
void shl_words(uint64_t* r, const uint64_t* x, unsigned s) noexcept
{
    for (size_t i = W - 1; i != 0; --i)
        r[i] = V::fshl(x[i], x[i - 1], s);
    r[0] = x[0] << s;
}

template <typename V, size_t W>
void shr_words(uint64_t* r, const uint64_t* x, unsigned s) noexcept
{
    for (size_t i = 1; i < W; ++i)
        r[i - 1] = V::fshr(x[i], x[i - 1], s);
    r[W - 1] = x[W - 1] >> s;
}

/// Word array shifts with the shift == 0 case handled outside of the per word loop.
template <typename V, size_t W>
void shl_words_hoisted(uint64_t* r, const uint64_t* x, unsigned s) noexcept
{
    if (s == 0)
    {
        for (size_t i = 0; i < W; ++i)
            r[i] = x[i];
        return;
    }
    const uint64_t ns = 64 - s;
    for (size_t i = W - 1; i != 0; --i)
        r[i] = V::fshl_nz(x[i], x[i - 1], s, ns);
    r[0] = x[0] << s;
}

template <typename V, size_t W>
void shr_words_hoisted(uint64_t* r, const uint64_t* x, unsigned s) noexcept
{
    if (s == 0)
    {
        for (size_t i = 0; i < W; ++i)
            r[i] = x[i];
        return;
    }
    const uint64_t ns = 64 - s;
    for (size_t i = 1; i < W; ++i)
        r[i - 1] = V::fshr_nz(x[i], x[i - 1], s, ns);
    r[W - 1] = x[W - 1] >> s;
}

template <typename V, size_t W, bool Left>
void words_hoisted(benchmark::State& state)
{
    const auto& in = get_inputs(state.range(0) != 0);
    std::vector<uint64_t> out(num_inputs * W);
    for ([[maybe_unused]] auto _ : state)
    {
        for (size_t i = 0; i < num_inputs; ++i)
        {
            if constexpr (Left)
                shl_words_hoisted<V, W>(&out[i * W], &in.words[i * W], in.shifts[i]);
            else
                shr_words_hoisted<V, W>(&out[i * W], &in.words[i * W], in.shifts[i]);
        }
        benchmark::DoNotOptimize(out.data());
        benchmark::ClobberMemory();
    }
    state.SetItemsProcessed(state.iterations() * static_cast<int64_t>(num_inputs));
}

template <typename V, size_t W, bool Left>
void words(benchmark::State& state)
{
    const auto& in = get_inputs(state.range(0) != 0);
    std::vector<uint64_t> out(num_inputs * W);
    for ([[maybe_unused]] auto _ : state)
    {
        for (size_t i = 0; i < num_inputs; ++i)
        {
            if constexpr (Left)
                shl_words<V, W>(&out[i * W], &in.words[i * W], in.shifts[i]);
            else
                shr_words<V, W>(&out[i * W], &in.words[i * W], in.shifts[i]);
        }
        benchmark::DoNotOptimize(out.data());
        benchmark::ClobberMemory();
    }
    state.SetItemsProcessed(state.iterations() * static_cast<int64_t>(num_inputs));
}
}  // namespace

#define SHLD_BENCH(V)                                \
    BENCHMARK(fsh_lat<V, true>)->DenseRange(0, 1);   \
    BENCHMARK(fsh_lat<V, false>)->DenseRange(0, 1);  \
    BENCHMARK(fsh_tput<V, true>)->DenseRange(0, 1);  \
    BENCHMARK(fsh_tput<V, false>)->DenseRange(0, 1); \
    BENCHMARK(words<V, 4, true>)->DenseRange(0, 1);  \
    BENCHMARK(words<V, 4, false>)->DenseRange(0, 1); \
    BENCHMARK(words<V, 8, true>)->DenseRange(0, 1);  \
    BENCHMARK(words<V, 8, false>)->DenseRange(0, 1)

#define HOISTED_BENCH(V)                                     \
    BENCHMARK(words_hoisted<V, 4, true>)->DenseRange(0, 1);  \
    BENCHMARK(words_hoisted<V, 4, false>)->DenseRange(0, 1); \
    BENCHMARK(words_hoisted<V, 8, true>)->DenseRange(0, 1);  \
    BENCHMARK(words_hoisted<V, 8, false>)->DenseRange(0, 1)

#if SHLD_BENCH_X86
SHLD_BENCH(shld_asm);
SHLD_BENCH(shift5_asm);
SHLD_BENCH(cmov_asm);
HOISTED_BENCH(bmi2_asm);
#endif
SHLD_BENCH(cxx);
HOISTED_BENCH(cxx_nz);
