// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <div.hpp>
#include <intx/intx.hpp>

#include "../utils/random.hpp"
#include <gtest/gtest.h>

#include "../utils/gmp.hpp"

using namespace intx;

namespace
{
inline uint64_t udiv_long(uint64_t uh, uint64_t ul, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(uh), "a"(ul), "g"(v));
    return q;
}

inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    return udiv_long(~d, ~uint64_t(0), d);
}
}  // namespace

TEST(div, normalize)
{
    uint512 u;
    uint512 v = 1;
    auto na = normalize64(u, v);
    EXPECT_EQ(na.shift, 63);
    EXPECT_EQ(na.num_denominator_words, 1);
    EXPECT_EQ(na.num_numerator_words, 0);
    EXPECT_EQ(na.numerator[0], 0);
    EXPECT_EQ(na.numerator[1], 0);
    EXPECT_EQ(na.numerator[16], 0);
    EXPECT_EQ(na.denominator[0], uint64_t{1} << 63);
    EXPECT_EQ(na.denominator[1], 0);

    u = uint512{1313, 1414};
    v = uint512{1212, 12};
    na = normalize64(u, v);
    EXPECT_EQ(na.shift, 60);
    EXPECT_EQ(na.num_denominator_words, 5);
    EXPECT_EQ(na.num_numerator_words, 5);
    EXPECT_EQ(na.numerator[0], uint64_t{1313} << 60);
    EXPECT_EQ(na.numerator[1], uint64_t{1313} >> (64 - 60));
    EXPECT_EQ(na.numerator[2], 0);
    EXPECT_EQ(na.numerator[4], uint64_t{1414} << 60);
    EXPECT_EQ(na.numerator[na.num_numerator_words], uint64_t{1414} >> (64 - 60));
    EXPECT_EQ(na.denominator[0], uint64_t{1212} << 60);
    EXPECT_EQ(na.denominator[1], uint64_t{1212} >> (64 - 60));
    EXPECT_EQ(na.denominator[2], 0);
    EXPECT_EQ(na.denominator[4], uint64_t{12} << 60);
    EXPECT_EQ(na.denominator[5], 0);

    u = shl(uint512{3}, 510);
    v = uint512{uint256{1, 0xffffffffffffffff}, 0};
    na = normalize64(u, v);
    EXPECT_EQ(na.shift, 0);
    EXPECT_EQ(na.num_denominator_words, 3);
    EXPECT_EQ(na.num_numerator_words, 8);
    EXPECT_EQ(na.numerator[0], 0);
    EXPECT_EQ(na.numerator[1], 0);
    EXPECT_EQ(na.numerator[2], 0);
    EXPECT_EQ(na.numerator[4], 0);
    EXPECT_EQ(na.numerator[7], uint64_t{3} << 62);
    EXPECT_EQ(na.numerator[8], 0);
    EXPECT_EQ(na.denominator[0], 1);
    EXPECT_EQ(na.denominator[1], 0);
    EXPECT_EQ(na.denominator[2], 0xffffffffffffffff);
    EXPECT_EQ(na.denominator[3], 0);

    u = shl(uint512{7}, 509);
    v = uint512{uint256{1, 0x3fffffffffffffff}, 0};
    na = normalize64(u, v);
    EXPECT_EQ(na.shift, 2);
    EXPECT_EQ(na.num_denominator_words, 3);
    EXPECT_EQ(na.num_numerator_words, 8);
    EXPECT_EQ(na.numerator[6], 0);
    EXPECT_EQ(na.numerator[7], uint64_t{1} << 63);
    EXPECT_EQ(na.numerator[8], 3);
    EXPECT_EQ(na.denominator[0], 4);
    EXPECT_EQ(na.denominator[1], 0);
    EXPECT_EQ(na.denominator[2], 0xfffffffffffffffc);
    EXPECT_EQ(na.denominator[3], 0);
}

template <typename Int>
struct div_test_case
{
    Int numerator;
    Int denominator;
    Int quotient;
    Int reminder;
};

static div_test_case<uint512> div_test_cases[] = {
    {2, 1, 2, 0},
    {
        0x10000000000000000_u512,
        2,
        0x8000000000000000_u512,
        0,
    },
    {
        0x478392145435897052_u512,
        0x111,
        0x430f89ebadad0baa,
        8,
    },
    {
        0x1e00000000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000009000000000000000000_u512,
        0xa,
        0x30000000000000000000000e6666666666666666666666666666666666666666666666666666666666666666666666666666666674ccccccccccccccccc_u512,
        8,
    },
    {
        0x767676767676767676000000767676767676_u512,
        0x2900760076761e00020076760000000076767676000000_u512,
        0,
        0x767676767676767676000000767676767676_u512,
    },
    {
        0x12121212121212121212121212121212_u512,
        0x232323232323232323_u512,
        0x83a83a83a83a83,
        0x171729292929292929_u512,
    },
    {
        0xabc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0_u512,
        0x1c01c01c01c01c01c01c01c01c_u512,
        0x621ed21ed21ed21ed21ed21ed224f40bf40bf40bf40bf40bf40bf46e12de12de12de12de12de12de1900000000000000000_u512,
        0xabc0abc0abc0abc0,
    },
    {
        0xfffff716b61616160b0b0b2b0b0b0becf4bef50a0df4f48b090b2b0bc60a0a00_u512,
        0xfffff716b61616160b0b0b2b0b230b000008010d0a2b00_u512,
        0xffffffffffffffffff_u512,
        0xfffff7169e17030ac1ff082ed51796090b330cd3143500_u512,
    },
    {
        0x50beb1c60141a0000dc2b0b0b0b0b0b410a0a0df4f40b090b2b0bc60a0a00_u512,
        0x2000110000000d0a300e750a000000090a0a_u512,
        0x285f437064cd09ff8bc5b7857d_u512,
        0x1fda1c384d86199e14bb4edfc6693042f11e_u512,
    },
    {
        0x4b00000b41000b0b0b2b0b0b0b0b0b410a0aeff4f40b090b2b0bc60a0a1000_u512,
        0x4b00000b41000b0b0b2b0b0b0b0b0b410a0aeff4f40b0a0a_u512,
        0xffffffffffffff_u512,
        0x4b00000b41000b0b0b2b0b0b0b0b0b400b35fbbafe151a0a_u512,
    },
};

TEST(div, udivrem_512)
{
    for (auto& t : div_test_cases)
    {
        auto res = udivrem(t.numerator, t.denominator);
        EXPECT_EQ(res.quot, t.quotient);
        EXPECT_EQ(res.rem, t.reminder);
    }
}


static div_test_case<uint256> sdivrem_test_cases[] = {
    {13_u256, 3_u256, 4_u256, 1_u256},
    {-13_u256, 3_u256, -4_u256, -1_u256},
    {13_u256, -3_u256, -4_u256, 1_u256},
    {-13_u256, -3_u256, 4_u256, -1_u256},
    {1_u256 << 255, -1_u256, 1_u256 << 255, 0},
};

TEST(div, sdivrem_256)
{
    for (auto& t : sdivrem_test_cases)
    {
        EXPECT_EQ(t.denominator * t.quotient + t.reminder, t.numerator);

        auto res = sdivrem(t.numerator, t.denominator);
        EXPECT_EQ(res.quot, t.quotient);
        EXPECT_EQ(res.rem, t.reminder);

        auto res2 = gmp::sdivrem(t.numerator, t.denominator);
        EXPECT_EQ(res2.quot, res.quot);
        EXPECT_EQ(res2.rem, res.rem);
    }
}

TEST(div, sdivrem_512)
{
    auto n = -13_u512;
    auto d = -3_u512;

    auto res = sdivrem(n, d);
    EXPECT_EQ(res.quot, 4_u512);
    EXPECT_EQ(res.rem, -1_u512);

    auto res2 = gmp::sdivrem(n, d);
    EXPECT_EQ(res2.quot, res.quot);
    EXPECT_EQ(res2.rem, res.rem);
}

TEST(div, reciprocal)
{
    constexpr auto n = 1000000;

    constexpr auto d_start = uint64_t{1} << 63;
    for (uint64_t d = d_start; d < d_start + n; ++d)
    {
        auto v = reciprocal(d);
        EXPECT_EQ(v, reciprocal_naive(d)) << d;
    }

    constexpr auto d_end = ~uint64_t{0};
    for (uint64_t d = d_end; d > d_end - n; --d)
    {
        auto v = reciprocal(d);
        EXPECT_EQ(v, reciprocal_naive(d)) << d;
    }
}
