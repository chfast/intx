// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/int128.hpp>

#include "../utils/random.hpp"
#include <gtest/gtest.h>

using namespace intx;

namespace
{
struct arith_test_case
{
    uint128 x;
    uint128 y;
    uint128 sum;
    uint128 difference;
    uint128 product;
};

constexpr arith_test_case arith_test_cases[] = {
    {0, 0, 0, 0, 0},
    {0, 1, 1, 0xffffffffffffffffffffffffffffffff_u128, 0},
    {1, 0, 1, 1, 0},
    {1, 1, 2, 0, 1},
    {1, 0xffffffffffffffff, {1, 0}, 0xffffffffffffffff0000000000000002_u128, 0xffffffffffffffff},
    {0xffffffffffffffff, 1, {1, 0}, 0xfffffffffffffffe, 0xffffffffffffffff},
    {0xffffffffffffffff, 0xffffffffffffffff, 0x1fffffffffffffffe_u128, 0,
        0xfffffffffffffffe0000000000000001_u128},
    {0x8000000000000000, 0x8000000000000000, {1, 0}, 0, 0x40000000000000000000000000000000_u128},
    {0x18000000000000000_u128, 0x8000000000000000, {2, 0}, {1, 0},
        0xc0000000000000000000000000000000_u128},
    {0x8000000000000000, 0x18000000000000000_u128, {2, 0}, 0xffffffffffffffff0000000000000000_u128,
        0xc0000000000000000000000000000000_u128},
    {{1, 0}, 0xffffffffffffffff, 0x1ffffffffffffffff_u128, 1, {0xffffffffffffffff, 0}},
    {{1, 0}, {1, 0}, {2, 0}, 0, 0},
};
}

void static_test_comparison()
{
    constexpr uint128 zero;
    constexpr uint128 zer0 = 0;
    constexpr uint128 one = 1;

    static_assert(zero == 0, "");
    static_assert(zero != 1, "");
    static_assert(one > 0, "");
    static_assert(one >= 0, "");
    static_assert(zero >= 0, "");
    static_assert(zero < 1, "");
    static_assert(zero <= 1, "");
    static_assert(zero <= 0, "");

    static_assert(zero == zer0, "");
    static_assert(zero != one, "");
    static_assert(one > zero, "");
    static_assert(one >= zero, "");
    static_assert(zero >= zer0, "");
    static_assert(zero < one, "");
    static_assert(zero <= one, "");
    static_assert(zero <= zer0, "");

    constexpr auto zero_one = uint128{0, 1};
    constexpr auto one_zero = uint128{1, 0};

    static_assert(!(zero_one == one_zero), "");
    static_assert(zero_one != one_zero, "");
    static_assert(zero_one < one_zero, "");
    static_assert(zero_one <= one_zero, "");
    static_assert(!(zero_one > one_zero), "");
    static_assert(!(zero_one >= one_zero), "");
}

void static_test_bitwise_operators()
{
    constexpr uint128 x{0x5555555555555555, 0x5555555555555555};
    constexpr uint128 y{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa};
    constexpr uint128 one = 1;
    constexpr uint128 zero = 0;

    static_assert((x | one) == x, "");
    static_assert((y | one) == uint128{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaab}, "");

    static_assert((x & one) == one, "");
    static_assert((y & one) == zero, "");

    static_assert((x ^ zero) == x, "");
    static_assert((x ^ one) == uint128{0x5555555555555555, 0x5555555555555554}, "");

    static_assert(~x == y, "");
}

void static_test_arith()
{
    constexpr uint128 a = 0x8000000000000000;
    constexpr auto s = a + a;
    static_assert(s == uint128{1, 0}, "");
    static_assert(s - a == a, "");
    static_assert(s - 0 == s, "");
    static_assert(s + 0 == s, "");
    static_assert(-uint128(1) == uint128{0xffffffffffffffff, 0xffffffffffffffff}, "");
    static_assert(0 - uint128(2) == uint128{0xffffffffffffffff, 0xfffffffffffffffe}, "");
    static_assert(uint128(13) - 17 == uint128{0xffffffffffffffff, 0xfffffffffffffffc}, "");

    static_assert(-a == (~a + 1), "");
    static_assert(+a == a, "");
}

TEST(int128, add)
{
    for (auto& t: arith_test_cases)
    {
        EXPECT_EQ(t.x + t.y, t.sum);
        EXPECT_EQ(t.y + t.x, t.sum);
    }
}

TEST(int128, sub)
{
    for (auto& t: arith_test_cases)
    {
        EXPECT_EQ(t.x - t.y, t.difference);
    }
}

TEST(int128, mul)
{
    for (auto& t: arith_test_cases)
    {
        EXPECT_EQ(t.x * t.y, t.product);
        EXPECT_EQ(t.y * t.x, t.product);
    }
}

TEST(int128, increment)
{
    constexpr auto IO = uint128{1, 0};
    constexpr auto Of = uint128{~uint64_t{0}};

    auto a = Of;
    EXPECT_EQ(++a, IO);
    EXPECT_EQ(a, IO);

    auto b = Of;
    EXPECT_EQ(b++, Of);
    EXPECT_EQ(b, IO);

    auto c = IO;
    EXPECT_EQ(--c, Of);
    EXPECT_EQ(c, Of);

    auto d = IO;
    EXPECT_EQ(d--, IO);
    EXPECT_EQ(d, Of);

}

TEST(int128, shl)
{
    constexpr uint128 x = 1;
    for (unsigned s = 0; s < 127; ++s)
        EXPECT_EQ(clz(x << s), 127 - s);

    static_assert((x << 128) == 0, "");
    static_assert((uint128(3) << 63) == uint128(1, uint64_t(1) << 63), "");
}

TEST(int128, shr)
{
    constexpr uint128 x = uint128(1) << 127;
    for (unsigned s = 0; s < 127; ++s)
        EXPECT_EQ(clz(x >> s), s);

    static_assert((x >> 128) == 0, "");
    static_assert((uint128(3, 0) >> 1) == uint128(1, uint64_t(1) << 63), "");
}

static const uint128 division_test_vectors[][2] = {
    {{0x8000000000000000, 1}, {0x8000000000000000, 1}},
    {{0x8000000000000000, 1}, {0x8000000000000001, 1}},
    {{0x8000000000000001, 1}, {0x8000000000000000, 1}},
    {{0x8000000000000000, 2}, {0x8000000000000000, 1}},
    {{0x8000000000000000, 1}, {0x8000000000000000, 2}},
    {{1, 5}, {0, 7}},
    {{1, 5}, {2, 7}},
    {{0xffffffffffffffff, 0xffffffffffffffff}, {1, 0xffffffffffffffff}},
    {{0xee657725ff64cd48, 0xb8fe188a09dc4f78}, {0, 3}},  // Worst case for shift divs.
    {{0xbaf3f54fc23ec50a, 0x8db107aae7021a11}, {1, 0xa8d309c2d1c0a3ab}},
    {{0x9af3f54fc23ec50a, 0x8db107aae7021a11}, {0xb5967a16d599854c, 0xa8d309c2d1c0a3ab}},
    {{0x395df916dfd1b5e, 0xe7e47d96b32ef2d5}, {0x537e3fbc5318dbc0, 0x38ae7c47ce8a620f}},
    {{0, 0x6dfed7df267e7ed0}, {0xb022a1a70b9cfbdf, 0xea31f3f6afbe6882}},
    {{0x62cbd6bebd625e29, 0}, {0x525661ea1ecad583, 0x39cb5e652a3a0656}},
    {{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, {0, 0xb92974ae3bfad96a}},
    {{0x657725ff64cd48, 0xb8fe188a09dc4f78}, {0, 0xb92974ae3bfad96a}},
    {{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, {0, 0xb92974ae3bfad9}},
    {{0xb1440f0ef70d4ef1, 0x2457e03b7d2cf0ac}, {0x5834d9e467cf238b, 0}},
    {{0xb1440f0ef70d4ef1, 0x2457e03b7d2cf0ac}, {1 << 13, 0}},
    {{0, 0}, {0xbb6376e43a291fef, 0xfee012e52194af52}},
    {{0, 0xdb7bf0efd05668d4}, {0, 0x510734f5eaa31a26}},
    {{0, 0xba8221b60d12e7c8}, {0x7dfb4ff3ec1e7777, 0}},
    {{0x6558ce6e35a99381, 0}, {0, 0xa08b35664c6dd38e}},
    {{0xac163d152c4f2345, 0}, {0x1b2e2e4a4c2227ff, 0}},
    {{0, 0}, {0, 0x2f7c95d0092581f6}},
    {{0, 0}, {0x7c0ee5320345187, 0}},
    {{1, 0xe7e47d96b32ef2d5}, {0x537e3fbc5318dbc0, 0}},
    {{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, {0, 1ul << 61}},
    {{0x9af3f54fc23ec50a, 0x8db107aae7021a11}, {0, 1}},
    {{0x1313131313131313, 0x0000000000000020}, {0x1313131313131313, 0x1313131313134013}},
    {{0xffffffffffffffff, 0xff00000000002100}, {0x000000000000ffff, 0xffffffffffffffff}},
    {{7567426269009013610, 5683582526294251485}, {637377717142870109, 905842064019625512}},
    {{17837195793149051481u, 13934821101650737475u}, {576552705938660309, 4226470430044458774}},
    {{0xe8e0eae8e8e8e8e5, 0xfffc000800000009}, {0, 0x000800091000e8e8}},
    {{0xe8e0eae8e8e8e8e5, 0xfffc000000000000}, {0, 0x000800090000e8e8}},
    {{0xffffffffffffffff, 0xff3f060e0e0e7a0a}, {0x10, 0x00000000401353ff}},
    {{0xffffffffffffffff, 0xf000000000000000}, {1, 0x40000000}},
    {{0xffffffffffffffff, 0xf000000000000000}, {1, 0x80000000}},
    {{0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f8f01}, {0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f}},
    {0xdac7fff9ffd9e1322626262626262600_u128, 0xd021262626262626},
    {0x100000000000004ff00000000a20000_u128, 0x100000000000000},
};

TEST(int128, div)
{
    int index = 0;
    for (auto& v : division_test_vectors)
    {
        auto q = v[0] / v[1];
        auto r = v[0] % v[1];

        auto x = ((unsigned __int128)v[0].hi << 64) | v[0].lo;
        auto y = ((unsigned __int128)v[1].hi << 64) | v[1].lo;
        auto nq = x / y;
        auto nr = x % y;
        uint128 eq{uint64_t(nq >> 64), uint64_t(nq)};
        uint128 er{uint64_t(nr >> 64), uint64_t(nr)};
        EXPECT_EQ(q, eq) << index;
        EXPECT_EQ(r, er) << index;

        auto res = udivrem(v[0], v[1]);
        EXPECT_EQ(res.quot, q) << index;
        EXPECT_EQ(res.rem, r) << index;

        index++;
    }
}

#ifdef __SIZEOF_INT128__
TEST(int128, arith_random_args)
{
    int c = 1000000;

    lcg<uint128> dist{get_seed()};

    while (c-- > 0)
    {
        auto x = dist();
        auto y = dist();

        auto s = x + y;
        auto d = x - y;
        auto p = x * y;
        auto q = x / y;
        auto r = x  % y;

        auto expected_s = uint128{(unsigned __int128){x} + (unsigned __int128){y}};
        auto expected_d = uint128{(unsigned __int128){x} - (unsigned __int128){y}};
        auto expected_p = uint128{(unsigned __int128){x} * (unsigned __int128){y}};
        auto expected_q = uint128{(unsigned __int128){x} / (unsigned __int128){y}};
        auto expected_r = uint128{(unsigned __int128){x} % (unsigned __int128){y}};

        EXPECT_EQ(s, expected_s) << c;
        EXPECT_EQ(d, expected_d) << c;
        EXPECT_EQ(p, expected_p) << c;
        EXPECT_EQ(q, expected_q) << c;
        EXPECT_EQ(r, expected_r) << c;
    }
}
#endif

TEST(int128, literals)
{
    auto a = 340282366920938463463374607431768211455_u128;
    EXPECT_EQ(a, (uint128{0xffffffffffffffff, 0xffffffffffffffff}));

    EXPECT_THROW(340282366920938463463374607431768211456_u128, std::overflow_error);
    EXPECT_THROW(3402823669209384634633746074317682114550_u128, std::overflow_error);

    a = 0xffffffffffffffffffffffffffffffff_u128;
    EXPECT_EQ(a, (uint128{0xffffffffffffffff, 0xffffffffffffffff}));

    EXPECT_THROW(0x100000000000000000000000000000000_u128, std::overflow_error);

    // Binary literals 0xb... are not supported yet.
    EXPECT_THROW(operator""_u128("0b1"), std::invalid_argument);

    EXPECT_THROW(operator""_u128("123x456"), std::invalid_argument);
    EXPECT_THROW(operator""_u128("0xabcxdef"), std::invalid_argument);

    EXPECT_EQ(0xaBc123eFd_u128, 0xAbC123EfD_u128);
}
