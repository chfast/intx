// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

#include "../utils/random.hpp"
#include <gtest/gtest.h>

using namespace intx;

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
}

TEST(int128, mul)
{
    uint128 zero;
    uint128 one = 1;
    uint128 two = 2;

    EXPECT_EQ(zero * zero, 0);
    EXPECT_EQ(zero * two, 0);
    EXPECT_EQ(one * one, 1);
    EXPECT_EQ(one * two, 2);

    uint128 f = 0xffffffffffffffff;
    EXPECT_EQ(f * f, uint128(0xfffffffffffffffe, 1));

    uint128 b1{1, 0};
    EXPECT_EQ(b1 * b1, zero);
    EXPECT_EQ(b1 * f, uint128(0xffffffffffffffff, 0));
}

#ifdef __SIZEOF_INT128__
TEST(int128, mul_random)
{
    size_t n = 10000;

    lcg<unsigned __int128> rng(get_seed());
    while (n-- > 0)
    {
        auto x = rng();
        auto y = rng();
        auto p = x * y;

        uint128 a{uint64_t(x >> 64), uint64_t(x)};
        uint128 b{uint64_t(y >> 64), uint64_t(y)};

        auto r = a * b;
        uint128 expected{uint64_t(p >> 64), uint64_t(p)};
        EXPECT_EQ(r, expected);
    }
}
#endif

TEST(int128, shl)
{
    uint128 x = 1;
    for (unsigned s = 0; s < 127; ++s)
        EXPECT_EQ(clz(x << s), 127 - s);

    static_assert((x << 128) == 0, "");
    static_assert((uint128(3) << 63) == uint128(1, uint64_t(1) << 63), "");
}

TEST(int128, shr)
{
    uint128 x = uint128(1) << 127;
    for (unsigned s = 0; s < 127; ++s)
        EXPECT_EQ(clz(x >> s), s);

    static_assert((x >> 128) == 0, "");
    static_assert((uint128(3, 0) >> 1) == uint128(1, uint64_t(1) << 63), "");
}

TEST(int128, div64)
{
    lcg<uint64_t> rng(get_seed());

    for (size_t i = 0; i < 1000; ++i)
    {
        auto x = rng();
        auto y = rng();

        auto e = x / y;
        EXPECT_EQ(uint128(x) / uint128(y), e) << x << " / " << y;
    }
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

        res = udivrem_by_reciprocal(v[0], v[1]);
        EXPECT_EQ(res.quot, q) << index;
        EXPECT_EQ(res.rem, r) << index;

        index++;
    }
}

TEST(int128, div_random)
{
    int c = 10000000;

    lcg<uint128> dist{get_seed()};

    while (c-- > 0)
    {
        auto x = dist();
        auto y = dist();
        auto r = x / y;

        auto nx = ((unsigned __int128)x.hi << 64) | x.lo;
        auto ny = ((unsigned __int128)y.hi << 64) | y.lo;
        auto s = nx / ny;
        EXPECT_EQ(r.hi, uint64_t(s >> 64)) << c;
        EXPECT_EQ(r.lo, uint64_t(s)) << c;
    }
}
