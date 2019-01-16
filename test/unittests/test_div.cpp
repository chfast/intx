// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

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
    auto na = normalize(u, v);
    EXPECT_EQ(na.shift, 31);
    EXPECT_EQ(na.num_denominator_words, 1);
    EXPECT_EQ(na.num_numerator_words, 0);
    EXPECT_EQ(na.numerator[0], 0);
    EXPECT_EQ(na.numerator[1], 0);
    EXPECT_EQ(na.numerator[16], 0);
    EXPECT_EQ(na.denominator[0], 1u << 31);
    EXPECT_EQ(na.denominator[1], 0);

    u = uint512{1313, 1414};
    v = uint512{1212, 12};
    na = normalize(u, v);
    EXPECT_EQ(na.shift, 28);
    EXPECT_EQ(na.num_denominator_words, 9);
    EXPECT_EQ(na.num_numerator_words, 9);
    EXPECT_EQ(na.numerator[0], 1313u << 28);
    EXPECT_EQ(na.numerator[1], 1313u >> (32 - 28));
    EXPECT_EQ(na.numerator[2], 0);
    EXPECT_EQ(na.numerator[8], 1414u << 28);
    EXPECT_EQ(na.numerator[na.num_numerator_words], 1414u >> (32 - 28));
    EXPECT_EQ(na.denominator[0], 1212u << 28);
    EXPECT_EQ(na.denominator[1], 1212u >> (32 - 28));
    EXPECT_EQ(na.denominator[2], 0);
    EXPECT_EQ(na.denominator[8], 12u << 28);
    EXPECT_EQ(na.denominator[9], 0);

    u = shl(uint512{3}, 510);
    v = uint512{uint256{1, 0xffffffff}, 0};
    na = normalize(u, v);
    EXPECT_EQ(na.shift, 0);
    EXPECT_EQ(na.num_denominator_words, 5);
    EXPECT_EQ(na.num_numerator_words, 16);
    EXPECT_EQ(na.numerator[0], 0);
    EXPECT_EQ(na.numerator[1], 0);
    EXPECT_EQ(na.numerator[2], 0);
    EXPECT_EQ(na.numerator[8], 0);
    EXPECT_EQ(na.numerator[15], 3 << 30);
    EXPECT_EQ(na.numerator[16], 0);
    EXPECT_EQ(na.denominator[0], 1);
    EXPECT_EQ(na.denominator[1], 0);
    EXPECT_EQ(na.denominator[2], 0);
    EXPECT_EQ(na.denominator[3], 0);
    EXPECT_EQ(na.denominator[4], 0xffffffff);
    EXPECT_EQ(na.denominator[5], 0);

    u = shl(uint512{7}, 509);
    v = uint512{uint256{1, 0x3fffffff}, 0};
    na = normalize(u, v);
    EXPECT_EQ(na.shift, 2);
    EXPECT_EQ(na.num_denominator_words, 5);
    EXPECT_EQ(na.num_numerator_words, 16);
    EXPECT_EQ(na.numerator[14], 0);
    EXPECT_EQ(na.numerator[15], 1 << 31);
    EXPECT_EQ(na.numerator[16], 3);
    EXPECT_EQ(na.denominator[0], 4);
    EXPECT_EQ(na.denominator[1], 0);
    EXPECT_EQ(na.denominator[2], 0);
    EXPECT_EQ(na.denominator[3], 0);
    EXPECT_EQ(na.denominator[4], 0xfffffffc);
    EXPECT_EQ(na.denominator[5], 0);
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
    {
        0x10000000000000000_u512,
        2,
        0x8000000000000000_u512,
        0,
    },
    {
        0x1e00000000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000009000000000000000000_u512,
        0xa,
        0x30000000000000000000000e6666666666666666666666666666666666666666666666666666666666666666666666666666666674ccccccccccccccccc_u512,
        8,
    },
};

TEST(div, udivrem_512)
{
    for (auto& t : div_test_cases)
    {
        uint512 q, r;
        std::tie(q, r) = udivrem(t.numerator, t.denominator);
        EXPECT_EQ(q, t.quotient);
        EXPECT_EQ(r, t.reminder);
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

        uint256 q, r;
        std::tie(q, r) = sdivrem(t.numerator, t.denominator);
        EXPECT_EQ(q, t.quotient);
        EXPECT_EQ(r, t.reminder);

        uint256 k, l;
        std::tie(k, l) = gmp::sdivrem(t.numerator, t.denominator);
        EXPECT_EQ(k, q);
        EXPECT_EQ(l, r);
    }
}

TEST(div, sdivrem_512)
{
    auto n = -13_u512;
    auto d = -3_u512;

    uint512 q, r;
    std::tie(q, r) = sdivrem(n, d);

    EXPECT_EQ(q, 4_u512);
    EXPECT_EQ(r, -1_u512);

    uint512 k, l;
    std::tie(k, l) = gmp::sdivrem(n, d);
    EXPECT_EQ(k, q);
    EXPECT_EQ(l, r);
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
