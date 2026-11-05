// intx: extended precision integer library.
// Copyright 2025 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"
#include <bit>
#include <random>
#include <vector>

using namespace intx;

namespace
{
/// The reference exponentiation: the plain square-and-multiply, mod 2^N.
/// This is the original implementation of intx::exp() (apart from the special case of base 2).
template <typename T>
constexpr T exp_reference(T base, T exponent) noexcept
{
    auto result = T{1};
    for (size_t i = bit_width(exponent); i > 0; --i)
    {
        result *= result;
        if (bit_test(exponent, i - 1))
            result *= base;
    }
    return result;
}

template <typename T>
T random_value(std::mt19937_64& rng)
{
    T x;
    for (size_t i = 0; i < T::num_words; ++i)
        x[i] = rng();
    return x;
}

/// Random value with the number of significant bits being exactly "width" (0 means the value 0).
template <typename T>
T random_with_width(std::mt19937_64& rng, unsigned width)
{
    if (width == 0)
        return 0;
    auto x = random_value<T>(rng);
    if (width < T::num_bits)
        x &= (T{1} << width) - 1;
    return x | (T{1} << (width - 1));
}

/// Random value of different shapes: dense, sparse, dense with runs of ones/zeros, any width.
template <typename T>
T random_exponent(std::mt19937_64& rng)
{
    const auto width = static_cast<unsigned>(rng() % (T::num_bits + 1));
    auto x = random_with_width<T>(rng, width);
    switch (rng() % 8)
    {
    case 0:  // Sparse.
        x &= random_value<T>(rng) & random_value<T>(rng) & random_value<T>(rng);
        break;
    case 1:  // Dense.
        x |= random_value<T>(rng) | random_value<T>(rng);
        if (width != 0 && width < T::num_bits)
            x &= (T{1} << width) - 1;
        break;
    case 2:  // Low bits all ones.
        x |= (T{1} << (rng() % T::num_bits)) - 1;
        if (width != 0 && width < T::num_bits)
            x &= (T{1} << width) - 1;
        break;
    default:
        break;
    }
    return x;
}

/// Random base of different shapes, and with the given parity if "parity" is 0 or 1 (2 = any).
template <typename T>
T random_base(std::mt19937_64& rng, unsigned parity)
{
    T b;
    switch (rng() % 10)
    {
    case 0:  // Small.
        b = T{rng() % 1024};
        break;
    case 1:  // Near zero or MAX.
        b = T{rng() % 16} * ((rng() & 1) ? ~T{} : T{1});
        break;
    case 2:  // Power of 2 +- small.
        b = (T{1} << (rng() % T::num_bits)) + T{rng() % 5} - T{2};
        break;
    case 3:  // Fixed residue mod 8.
        b = (random_value<T>(rng) & ~T{7}) | T{rng() % 8};
        break;
    default:
        b = random_value<T>(rng);
        break;
    }
    if (parity <= 1)
        b = (b & ~T{1}) | T{parity};
    return b;
}

/// The exponents interesting for exponent reduction and early exits for the given width.
template <typename T>
std::vector<T> interesting_exponents()
{
    constexpr auto bits = T::num_bits;
    std::vector<T> es;
    for (uint64_t i = 0; i < 8; ++i)
        es.emplace_back(i);
    // Around the all multiples of N and powers of 2 up to 2N.
    for (const uint64_t c : {uint64_t{bits}, uint64_t{2 * bits}, uint64_t{std::bit_ceil(bits)},
             uint64_t{2 * std::bit_ceil(bits)}})
    {
        for (uint64_t d = 0; d < 7; ++d)
        {
            es.emplace_back(c - 3 + d);
        }
    }
    // Powers of 2 and their neighbours.
    for (unsigned k = 0; k < bits; ++k)
    {
        const auto p = T{1} << k;
        es.push_back(p);
        es.push_back(p - 1);
        es.push_back(p + 1);
        if (k < 4 || k + 4 >= bits || k == bits / 2)
        {
            es.push_back(~T{} - p);
            es.push_back(~T{} ^ p);
        }
    }
    es.push_back(~T{});
    es.push_back(T{1} << (bits - 1));
    es.push_back((T{3} << (bits - 2)) | 1);
    return es;
}

template <typename T>
std::vector<T> interesting_bases()
{
    constexpr auto bits = T::num_bits;
    std::vector<T> bs;
    for (uint64_t i = 0; i < 20; ++i)
    {
        bs.emplace_back(i);
        bs.push_back(-T{i});
    }
    bs.emplace_back(136279841);
    for (unsigned k : {2u, 3u, 4u, 5u, 7u, 8u, 31u, 32u, 33u, 63u, 64u, 65u, bits / 2, bits - 3,
             bits - 2, bits - 1})
    {
        const auto p = T{1} << k;
        bs.push_back(p);
        bs.push_back(p - 1);
        bs.push_back(p + 1);
        bs.push_back(-p);
        bs.push_back(-p + 1);
        bs.push_back(-p - 1);
    }
    return bs;
}

template <typename T>
void check(const T& base, const T& exponent)
{
    const auto expected = exp_reference(base, exponent);
    const auto result = exp(base, exponent);
    ASSERT_EQ(result, expected) << "base: " << hex(base) << "\nexponent: " << hex(exponent);
}
}  // namespace

TYPED_TEST(uint_test, exp_edge_cases)
{
    using T = TypeParam;
    const auto bases = interesting_bases<T>();
    const auto exponents = interesting_exponents<T>();
    for (const auto& b : bases)
    {
        for (const auto& e : exponents)
        {
            check(b, e);
            if (::testing::Test::HasFatalFailure())
                return;
        }
    }
}

TYPED_TEST(uint_test, exp_even_base_large_exponent)
{
    // Even base with exponent >= N always gives 0.
    using T = TypeParam;
    std::mt19937_64 rng{1};
    for (int i = 0; i < 2000; ++i)
    {
        const auto b = random_base<T>(rng, 0);
        const auto e =
            T{uint64_t{T::num_bits} + (rng() % 3 ? 0 : 1000)} + (random_exponent<T>(rng) >> 2);
        if (e < T::num_bits)
            continue;
        EXPECT_EQ(exp(b, e), 0) << hex(b) << " " << hex(e);
        EXPECT_EQ(exp(b, e), exp_reference(b, e));
    }
}

TYPED_TEST(uint_test, exp_odd_base_exponent_high_bits)
{
    // Odd base: the top 2 bits of the exponent must not matter (Carmichael function of 2^N).
    using T = TypeParam;
    std::mt19937_64 rng{2};
    constexpr auto top2 = T{3} << (T::num_bits - 2);
    for (int i = 0; i < 3000; ++i)
    {
        const auto b = random_base<T>(rng, 1);
        const auto e = random_exponent<T>(rng) & ~top2;
        for (const auto& hi : {T{0}, T{1} << (T::num_bits - 2), T{1} << (T::num_bits - 1), top2})
        {
            const auto r = exp(b, e | hi);
            ASSERT_EQ(r, exp_reference(b, e | hi)) << hex(b) << " " << hex(e | hi);
            ASSERT_EQ(r, exp_reference(b, e)) << hex(b) << " " << hex(e | hi);
        }
    }
}

namespace
{
template <typename T>
void random_differential(unsigned seed, int count)
{
    std::mt19937_64 rng{seed};
    for (int i = 0; i < count; ++i)
    {
        const auto parity = static_cast<unsigned>(rng() % 3);  // 2 means any.
        const auto b = random_base<T>(rng, parity);
        const auto e = random_exponent<T>(rng);
        check(b, e);
        if (::testing::Test::HasFatalFailure())
            return;
    }
}
}  // namespace

TYPED_TEST(uint_test, exp_odd_base_all_exponent_widths)
{
    // Odd bases with every residue mod 8 and the exponents of every bit width,
    // also with the all-ones and the single-bit patterns.
    using T = TypeParam;
    std::mt19937_64 rng{4};
    for (unsigned width = 0; width <= T::num_bits; ++width)
    {
        for (const uint64_t residue : {uint64_t{1}, uint64_t{3}, uint64_t{5}, uint64_t{7}})
        {
            for (int i = 0; i < 4; ++i)
            {
                const auto b = (random_value<T>(rng) & ~T{7}) | T{residue};
                check(b, random_with_width<T>(rng, width));
                if (width != 0)
                {
                    const auto top = T{1} << (width - 1);
                    check(b, top);
                    check(b, top | (top - 1));
                }
            }
            if (::testing::Test::HasFatalFailure())
                return;
        }
    }
}

TYPED_TEST(uint_test, exp_random_differential)
{
    random_differential<TypeParam>(3, TypeParam::num_bits == 256 ? 1000000 : 100000);
}

TEST(uint256, exp_constexpr)
{
    static_assert(exp(0_u256, 0_u256) == 1);
    static_assert(exp(0_u256, 1_u256) == 0);
    static_assert(exp(2_u256, 255_u256) == (1_u256 << 255));
    static_assert(exp(3_u256, 5_u256) == 243);
    static_assert(exp(3_u256, ~0_u256) ==
                  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab_u256);
    static_assert(exp(6_u256, 300_u256) == 0);
    static_assert(exp(6_u256, 255_u256) == exp_reference(6_u256, 255_u256));
    static_assert(exp(0x123456789abcdef1_u256, 0xfedcba9876543210fedcba98765432_u256) ==
                  exp_reference(0x123456789abcdef1_u256, 0xfedcba9876543210fedcba98765432_u256));
    static_assert(
        exp(0xfffffffffffffffffffffff7_u256, 0x3fffffffffffffffffffffffffffffffffffffffffff_u256) ==
        exp_reference(
            0xfffffffffffffffffffffff7_u256, 0x3fffffffffffffffffffffffffffffffffffffffffff_u256));
}
