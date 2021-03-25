// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_utils.hpp"
#include <gtest/gtest.h>
#include <intx/int128.hpp>

#pragma warning(disable : 4307)

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
    {1, 0xffffffffffffffff, X{1, 0}, 0xffffffffffffffff0000000000000002_u128, 0xffffffffffffffff},
    {0xffffffffffffffff, 1, X{1, 0}, 0xfffffffffffffffe, 0xffffffffffffffff},
    {0xffffffffffffffff, 0xffffffffffffffff, 0x1fffffffffffffffe_u128, 0,
        0xfffffffffffffffe0000000000000001_u128},
    {0x8000000000000000, 0x8000000000000000, X{1, 0}, 0, 0x40000000000000000000000000000000_u128},
    {0x18000000000000000_u128, 0x8000000000000000, X{2, 0}, X{1, 0},
        0xc0000000000000000000000000000000_u128},
    {0x8000000000000000, 0x18000000000000000_u128, X{2, 0}, 0xffffffffffffffff0000000000000000_u128,
        0xc0000000000000000000000000000000_u128},
    {X{1, 0}, 0xffffffffffffffff, 0x1ffffffffffffffff_u128, 1, X{0xffffffffffffffff, 0}},
    {X{1, 0}, X{1, 0}, X{2, 0}, 0, 0},
};


struct div_test_case
{
    uint128 x;
    uint128 y;
    uint128 quotient;
    uint128 reminder;
};

constexpr div_test_case div_test_cases[] = {
    {X{0x8000000000000000, 1}, X{0x8000000000000000, 1}, 1, 0},
    {X{0x8000000000000000, 1}, X{0x8000000000000001, 1}, 0, X{0x8000000000000000, 1}},
    {X{0x8000000000000001, 1}, X{0x8000000000000000, 1}, 1, X{1, 0}},
    {X{0x8000000000000000, 2}, X{0x8000000000000000, 1}, 1, 1},
    {X{0x8000000000000000, 1}, X{0x8000000000000000, 2}, 0, X{0x8000000000000000, 1}},
    {X{1, 5}, 7, 0x2492492492492493, 0},
    {X{1, 5}, X{2, 7}, 0, X{1, 5}},
    {X{0xffffffffffffffff, 0xffffffffffffffff}, X{1, 0xffffffffffffffff}, 0x8000000000000000,
        0x7fffffffffffffff},
    {X{0xee657725ff64cd48, 0xb8fe188a09dc4f78}, 3, X{0x4f7727b7552199c2, 0xe854b2d8adf41a7d}, 1},
    {X{0xbaf3f54fc23ec50a, 0x8db107aae7021a11}, X{1, 0xa8d309c2d1c0a3ab}, 0x70a8814961f0fe6e,
        0x8c95107768881c97},
    {X{0x9af3f54fc23ec50a, 0x8db107aae7021a11}, X{0xb5967a16d599854c, 0xa8d309c2d1c0a3ab}, 0,
        X{0x9af3f54fc23ec50a, 0x8db107aae7021a11}},
    {X{0x395df916dfd1b5e, 0xe7e47d96b32ef2d5}, X{0x537e3fbc5318dbc0, 0x38ae7c47ce8a620f}, 0,
        X{0x395df916dfd1b5e, 0xe7e47d96b32ef2d5}},
    {0x6dfed7df267e7ed0, X{0xb022a1a70b9cfbdf, 0xea31f3f6afbe6882}, 0, 0x6dfed7df267e7ed0},
    {X{0x62cbd6bebd625e29, 0}, X{0x525661ea1ecad583, 0x39cb5e652a3a0656}, 1,
        X{0x107574d49e9788a5, 0xc634a19ad5c5f9aa}},
    {X{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, 0xb92974ae3bfad96a, 0x8c488dc0d0453a78,
        0x41bb80845d7261c8},
    {X{0x657725ff64cd48, 0xb8fe188a09dc4f78}, 0xb92974ae3bfad96a, 0x8c488dc0d0453a,
        0xa25244a3b04d7b74},
    {X{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, 0xb92974ae3bfad9, X{0x8c, 0x488dc0d0453ac8a9},
        0x955de0d6202e37},
    {X{0xb1440f0ef70d4ef1, 0x2457e03b7d2cf0ac}, X{0x5834d9e467cf238b, 0}, 2,
        X{0xda5b46276f07db, 0x2457e03b7d2cf0ac}},
    {X{0xb1440f0ef70d4ef1, 0x2457e03b7d2cf0ac}, X{0x2000, 0}, 0x58a207877b86a,
        X{0xef1, 0x2457e03b7d2cf0ac}},
    {0, X{0xbb6376e43a291fef, 0xfee012e52194af52}, 0, 0},
    {0xdb7bf0efd05668d4, 0x510734f5eaa31a26, 2, 0x396d8703fb103488},
    {0xba8221b60d12e7c8, X{0x7dfb4ff3ec1e7777, 0}, 0, 0xba8221b60d12e7c8},
    {X{0x6558ce6e35a99381, 0}, 0xa08b35664c6dd38e, 0xa19b159fa722dbc7, 0x6a1e234ee7ca129e},
    {X{0xac163d152c4f2345, 0}, X{0x1b2e2e4a4c2227ff, 0}, 6, X{0x90127576382334b, 0}},
    {0, 0x2f7c95d0092581f6, 0, 0},
    {0, X{0x7c0ee5320345187, 0}, 0, 0},
    {X{1, 0xe7e47d96b32ef2d5}, X{0x537e3fbc5318dbc0, 0}, 0, X{1, 0xe7e47d96b32ef2d5}},
    {X{0x657725ff64cd486d, 0xb8fe188a09dc4f78}, 0x2000000000000000, X{3, 0x2bb92ffb266a436d},
        0x18fe188a09dc4f78},
    {X{0x9af3f54fc23ec50a, 0x8db107aae7021a11}, 1, X{0x9af3f54fc23ec50a, 0x8db107aae7021a11}, 0},
    {X{0x1313131313131313, 0x20}, X{0x1313131313131313, 0x1313131313134013}, 0,
        X{0x1313131313131313, 0x20}},
    {X{0xffffffffffffffff, 0xff00000000002100}, X{0xffff, 0xffffffffffffffff}, 0xffffffffffff,
        X{0xffff, 0xff010000000020ff}},
    {X{0x6904e619043deb6a, 0x4ee02431db62d7dd}, X{0x8d86ba8220cd85d, 0xc92328ed07f1628}, 0xb,
        X{0x7b845df8db09f6a, 0xc497f80ee5ece425}},
    {X{0xf78a73117fbdc259, 0xc1626df64c827943}, X{0x80053a19fc39bd5, 0x3aa770769c7e0f16}, 0x1e,
        X{0x780a620c6d17f5c, 0xe1c3400ff5bcb4af}},
    {X{0xe8e0eae8e8e8e8e5, 0xfffc000800000009}, 0x800091000e8e8, X{0x1d1b, 0xfc6365e50bec6eb0},
        0x16a8bed6c3089},
    {X{0xe8e0eae8e8e8e8e5, 0xfffc000000000000}, 0x800090000e8e8, X{0x1d1b, 0xfc9d9d9c540368c6},
        0xcf3ac5f59c90},
    {X{0xffffffffffffffff, 0xff3f060e0e0e7a0a}, X{0x10, 0x401353ff}, 0xfffffffffbfecac,
        0xf4f0fb98361f6b6},
    {X{0xffffffffffffffff, 0xf000000000000000}, X{1, 0x40000000}, 0xffffffffc0000000, 0},
    {X{0xffffffffffffffff, 0xf000000000000000}, X{1, 0x80000000}, 0xffffffff80000000,
        0x3000000000000000},
    {X{0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f8f01}, X{0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f}, 1, 0x7ff2},
    {X{0xdac7fff9ffd9e132, 0x2626262626262600}, 0xd021262626262626, X{1, 0xd1a094108c5da55},
        0x6f386ccc73c11f62},
    {X{0x100000000000004, 0xff00000000a20000}, 0x100000000000000, X{1, 0x4ff}, 0xa20000},
};
}  // namespace

namespace static_test_comparison
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

constexpr auto zero_one = uint128{1};
constexpr auto one_zero = uint128{X{1, 0}};

static_assert(!(zero_one == one_zero), "");
static_assert(zero_one != one_zero, "");
static_assert(zero_one < one_zero, "");
static_assert(zero_one <= one_zero, "");
static_assert(!(zero_one > one_zero), "");
static_assert(!(zero_one >= one_zero), "");
}  // namespace static_test_comparison

namespace static_test_bitwise_operators
{
constexpr uint128 x{X{0x5555555555555555, 0x5555555555555555}};
constexpr uint128 y{X{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa}};
constexpr uint128 one = 1;
constexpr uint128 zero = 0;

static_assert((x | one) == x, "");
static_assert((y | one) == uint128{X{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaab}}, "");

static_assert((x & one) == one, "");
static_assert((y & one) == zero, "");

static_assert((x ^ zero) == x, "");
static_assert((x ^ one) == uint128{X{0x5555555555555555, 0x5555555555555554}}, "");

static_assert(~x == y, "");
}  // namespace static_test_bitwise_operators

namespace static_test_explicit_conversion_to_bool
{
static_assert(uint128{X{1, 0}}, "");
static_assert(uint128{X{0, 1}}, "");
static_assert(uint128{X{1, 1}}, "");
static_assert(!uint128{X{0, 0}}, "");
static_assert(!static_cast<bool>(uint128{0}), "");
}  // namespace static_test_explicit_conversion_to_bool

#ifndef _MSC_VER
// FIXME: Investigate "integer constant overflow" issue on MSVC.
namespace static_test_arith
{
constexpr auto a = uint128{0x8000000000000000};
constexpr auto s = a + a;
static_assert(s == uint128{X{1, 0}}, "");
static_assert(s - a == a, "");
static_assert(s - 0 == s, "");
static_assert(s + 0 == s, "");
static_assert(-uint128(1) == uint128{X{0xffffffffffffffff, 0xffffffffffffffff}}, "");
static_assert(0 - uint128(2) == uint128{X{0xffffffffffffffff, 0xfffffffffffffffe}}, "");
static_assert(uint128(13) - 17 == uint128{X{0xffffffffffffffff, 0xfffffffffffffffc}}, "");

static_assert(-a == (~a + 1), "");
static_assert(+a == a, "");
}  // namespace static_test_arith
#endif

TEST(int128, numeric_limits)
{
    static_assert(!std::numeric_limits<uint128>::is_signed, "");
    static_assert(std::numeric_limits<uint128>::is_integer, "");
    static_assert(std::numeric_limits<uint128>::is_exact, "");
    static_assert(std::numeric_limits<uint128>::radix == 2, "");

    static_assert(std::numeric_limits<uint128>::digits10 == 38, "");
    static_assert(std::numeric_limits<uint128>::min() == 0, "");
    static_assert(std::numeric_limits<uint128>::max() == uint128{0} - 1, "");

    EXPECT_EQ(std::numeric_limits<uint128>::min(), 0);
    EXPECT_EQ(std::numeric_limits<uint128>::max(), uint128{0} - 1);
}

TEST(int128, add)
{
    for (const auto& t : arith_test_cases)
    {
        EXPECT_EQ(t.x + t.y, t.sum);
        EXPECT_EQ(t.y + t.x, t.sum);
    }
}

TEST(int128, sub)
{
    for (const auto& t : arith_test_cases)
    {
        EXPECT_EQ(t.x - t.y, t.difference);
    }
}

TEST(int128, mul)
{
    for (const auto& t : arith_test_cases)
    {
        EXPECT_EQ(t.x * t.y, t.product);
        EXPECT_EQ(t.y * t.x, t.product);
        auto z = t.x;
        EXPECT_EQ(z *= t.y, t.product);
        EXPECT_EQ(z, t.product);
    }
}

TEST(int128, increment)
{
    constexpr auto IO = uint128{X{1, 0}};
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

    unsigned sh = 128;
    EXPECT_EQ(x << sh, 0);
    auto y = x;
    EXPECT_EQ(y << sh, 0);
    y = ~uint128{0};
    EXPECT_EQ(y << sh, 0);

    static_assert((x << 128) == 0, "");
    static_assert((uint128(3) << 63) == uint128(X{1, uint64_t(1) << 63}), "");

    auto z = uint128{2};
    EXPECT_EQ(z <<= 63, uint128(X{1, 0}));
    EXPECT_EQ(z, uint128(X{1, 0}));
}

TEST(int128, shr)
{
    constexpr uint128 x = uint128(1) << 127;
    for (unsigned s = 0; s < 127; ++s)
    {
        const auto result = x >> s;
        EXPECT_EQ(clz(result), s);
        EXPECT_EQ(x >> uint128{s}, result);
    }

    unsigned sh = 128;
    EXPECT_EQ(x >> sh, 0);
    EXPECT_EQ(x >> uint128{sh}, 0);
    auto y = x;
    EXPECT_EQ(y >> sh, 0);
    EXPECT_EQ(y >> uint128{sh}, 0);
    y = ~uint128{0};
    EXPECT_EQ(y >> sh, 0);
    EXPECT_EQ(y >> uint128{sh}, 0);
    EXPECT_EQ(y >> uint128(X{1, 0}), 0);

    static_assert((x >> 128) == 0, "");
    static_assert((uint128(X{3, 0}) >> 1) == uint128(X{1, uint64_t(1) << 63}), "");

    auto z = uint128{X{1, 0}};
    EXPECT_EQ(z >>= 63, 2);
    EXPECT_EQ(z, 2);
}

TEST(int128, div)
{
    int index = 0;
    for (const auto& t : div_test_cases)
    {
        auto q = t.x / t.y;
        auto r = t.x % t.y;

        EXPECT_EQ(q, t.quotient) << index;
        EXPECT_EQ(r, t.reminder) << index;

        auto res = udivrem(t.x, t.y);
        EXPECT_EQ(res.quot, q) << index;
        EXPECT_EQ(res.rem, r) << index;

        index++;
    }
}

TEST(int128, sdivrem)
{
    const auto x = 0x83017fa6deecda0063b1977_u128;
    const auto y = 0x1bc83504ea8f7_u128;

    EXPECT_EQ(-x, 0xfffffffff7cfe8059211325ff9c4e689_u128);
    EXPECT_EQ(-y, 0xfffffffffffffffffffe437cafb15709_u128);

    EXPECT_EQ(sdivrem(x, y).quot, 0x4b729f5338f);
    EXPECT_EQ(sdivrem(x, y).rem, 0x13e5e3b3e827e);

    EXPECT_EQ(sdivrem(-x, -y).quot, 0x4b729f5338f);
    EXPECT_EQ(sdivrem(-x, -y).rem, 0xfffffffffffffffffffec1a1c4c17d82_u128);

    EXPECT_EQ(sdivrem(-x, y).quot, 0xfffffffffffffffffffffb48d60acc71_u128);
    EXPECT_EQ(sdivrem(-x, y).rem, 0xfffffffffffffffffffec1a1c4c17d82_u128);

    EXPECT_EQ(sdivrem(x, -y).quot, 0xfffffffffffffffffffffb48d60acc71_u128);
    EXPECT_EQ(sdivrem(x, -y).rem, 0x13e5e3b3e827e);
}

TEST(int128, literals)
{
    auto a = 340282366920938463463374607431768211455_u128;
    EXPECT_EQ(a, (uint128{X{0xffffffffffffffff, 0xffffffffffffffff}}));

    a = 0xffffffffffffffffffffffffffffffff_u128;
    EXPECT_EQ(a, (uint128{X{0xffffffffffffffff, 0xffffffffffffffff}}));

    EXPECT_EQ(0xaBc123eFd_u128, 0xAbC123EfD_u128);
}

TEST(int128, from_string)
{
    constexpr auto ka = from_string<uint128>("18446744073709551617");
    static_assert(ka == uint128{X{1, 1}}, "");
    const auto* const sa = "18446744073709551617";
    const auto a = from_string<uint128>(sa);
    EXPECT_EQ(a, uint128(X{1, 1}));

    constexpr auto kb = from_string<uint128>("0x300aabbccddeeff99");
    static_assert(kb == uint128{X{3, 0xaabbccddeeff99}}, "");
    const auto* const sb = "0x300aabbccddeeff99";
    EXPECT_EQ(from_string<uint128>(sb), uint128(X{3, 0xaabbccddeeff99}));
}

TEST(int128, literals_exceptions)
{
    EXPECT_THROW_MESSAGE(340282366920938463463374607431768211456_u128, std::out_of_range,
        "340282366920938463463374607431768211456");
    EXPECT_THROW_MESSAGE(3402823669209384634633746074317682114550_u128, std::out_of_range,
        "3402823669209384634633746074317682114550");

    EXPECT_THROW_MESSAGE(0x100000000000000000000000000000000_u128, std::out_of_range,
        "0x100000000000000000000000000000000");

    // Binary literals 0xb... are not supported yet.
    EXPECT_THROW_MESSAGE(operator""_u128("0b1"), std::invalid_argument, "invalid digit");
    EXPECT_THROW_MESSAGE(0b1010_u128, std::invalid_argument, "invalid digit");

    EXPECT_THROW_MESSAGE(operator""_u128("123x456"), std::invalid_argument, "invalid digit");
    EXPECT_THROW_MESSAGE(operator""_u128("0xabcxdef"), std::invalid_argument, "invalid digit");
}

TEST(int128, from_string_exceptions)
{
    EXPECT_THROW_MESSAGE(from_string<uint128>("123a"), std::invalid_argument, "invalid digit");
    EXPECT_THROW_MESSAGE(from_string<uint128>("0xcdefg"), std::invalid_argument, "invalid digit");
}

TEST(int128, to_string)
{
    EXPECT_EQ(to_string(uint128{33}, 33), "10");
    EXPECT_EQ(hex(uint128{7 * 16 + 1}), "71");
}

TEST(int128, umul)
{
    constexpr uint64_t inputs[] = {12243, 12503, 53501, 62950, 682017770, 1164206252, 1693374163,
        2079516117, 7043980147839196358, 12005172997151200154u, 15099684930315651455u,
        17254606825257761760u};
    constexpr uint128 outputs[] = {
        intx::umul(inputs[0], inputs[1]),
        intx::umul(inputs[1], inputs[2]),
        intx::umul(inputs[2], inputs[3]),
        intx::umul(inputs[3], inputs[4]),
        intx::umul(inputs[4], inputs[5]),
        intx::umul(inputs[5], inputs[6]),
        intx::umul(inputs[6], inputs[7]),
        intx::umul(inputs[7], inputs[8]),
        intx::umul(inputs[8], inputs[9]),
        intx::umul(inputs[9], inputs[10]),
        intx::umul(inputs[10], inputs[11]),
    };

    for (size_t i = 1; i < (sizeof(inputs) / sizeof(inputs[0])); ++i)
    {
        const auto x = inputs[i - 1];
        const auto y = inputs[i];

        const auto generic = outputs[i - 1];
        const auto best = intx::umul(x, y);

        EXPECT_EQ(generic, best) << x << " x " << y;
        EXPECT_EQ(generic[0], x * y);
    }
}

TEST(int128, clz)
{
    EXPECT_EQ(clz(intx::uint128{0}), 128u);
    for (unsigned i = 0; i < intx::uint128::num_bits; ++i)
    {
        const auto input = (intx::uint128{1} << (intx::uint128::num_bits - 1)) >> i;
        EXPECT_EQ(clz(input), i);
    }
}

TEST(int128, unary_plus)
{
    const auto x = uint128{1};
    const auto& y = +x;
    EXPECT_EQ(x, y);
    EXPECT_NE(&x, &y);
}
