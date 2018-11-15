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
    size_t n = 1000;

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

TEST(int128, clz)
{
    uint128 x = 1;
    EXPECT_EQ(clz(x), 127);
}
