// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace intx;

TEST(div, normalize)
{
    uint512 u;
    uint512 v = 1;
    auto na = internal::normalize(u, v);
    EXPECT_EQ(na.shift, 63u);
    EXPECT_EQ(na.num_divisor_words, 1);
    EXPECT_EQ(na.num_numerator_words, 0);
    EXPECT_EQ(na.numerator, 0);
    EXPECT_EQ(na.divisor, v << 63);

    u = uint512{1313, 0, 0, 0, 1414, 0, 0, 0};
    v = uint512{1212, 0, 0, 0, 12, 0, 0, 0};
    na = internal::normalize(u, v);
    EXPECT_EQ(na.shift, 60u);
    EXPECT_EQ(na.num_divisor_words, 5);
    EXPECT_EQ(na.num_numerator_words, 6);
    EXPECT_EQ(na.numerator, u << 60);
    EXPECT_EQ(na.divisor, v << 60);

    u = uint512{3} << 510;
    v = uint256{1, 0, 0xffffffffffffffff, 0};
    na = internal::normalize(u, v);
    EXPECT_EQ(na.shift, 0u);
    EXPECT_EQ(na.num_divisor_words, 3);
    EXPECT_EQ(na.num_numerator_words, 8);
    EXPECT_EQ(na.numerator, u);
    EXPECT_EQ(na.divisor, v);

    u = uint512{7} << 509;
    v = uint256{1, 0, 0x3fffffffffffffff, 0};
    na = internal::normalize(u, v);
    EXPECT_EQ(na.shift, 2u);
    EXPECT_EQ(na.num_divisor_words, 3);
    EXPECT_EQ(na.num_numerator_words, 9);
    EXPECT_EQ(na.numerator, intx::uint<576>{u} << 2);
    EXPECT_EQ(na.divisor, v << 2);
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
        0x7000000000000000,
        0x8000000000000000,
        0,
        0x7000000000000000,
    },
    {
        0x8000000000000000,
        0x8000000000000000,
        1,
        0,
    },
    {
        0x8000000000000001,
        0x8000000000000000,
        1,
        1,
    },
    {
        0x80000000000000010000000000000000_u128,
        0x80000000000000000000000000000000_u128,
        1,
        0x10000000000000000_u128,
    },
    {
        0x80000000000000000000000000000000_u128,
        0x80000000000000000000000000000001_u128,
        0,
        0x80000000000000000000000000000000_u128,
    },
    {
        0x478392145435897052_u512,
        0x111,
        0x430f89ebadad0baa,
        8,
    },
    {
        0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000_u512,
        0x800000000000000000000000000000000000000000000000_u512,
        0x800000000000000000000000000000000000000000000000_u512,
        0,
    },
    {
        0x80000000000000000000000000000000000000000000000000000000000000000000000000000000_u512,
        0x800000000000000000000000000000000000000000000000_u512,
        0x100000000000000000000000000000000_u512,
        0,
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
    {
        0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_u512,
        7,
        0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222_u512,
        0,
    },
    {
        0xf6376770abd3a36b20394c5664afef1194c801c3f05e42566f085ed24d002bb0_u512,
        0xb368d219438b7f3f,
        0x15f53bce87e9fb63c7c3ab03f6c0ba30d3ecf982fa97cdf0a_u512,
        0x4bfd94dbec31523a,
    },
    {
        0x0_u512,
        0x10900000000000000000000000000000000000000000000000000_u512,
        0x0_u512,
        0x0_u512,
    },
    {
        0x77676767676760000000000000001002e000000000000040000000e000000000000007f0000000000000000000000000000000000000000f7000000000000_u512,
        0xfffc000000000000767676240000000000002b05760476000000000000000000767676767600000000000000000000000000000000_u512,
        0x7769450c7b994e65025_u512,
        0x241cb1aa4f67c22ae65c9920bf3bb7ad8280311a887aee8be4054a3e242a5ea9ab35d800f2000000000000000000f7000000000000_u512,
    },
    {
        0xdffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000001000000000000000000000000008100000000001001_u512,
        0xdffffffffffffffffffffffffffffffffffffffffffff3fffffffffffffffffffffffffffff_u512,
        0xffffffffffffffffffffffffffffffffffedb6db6db6e9_u512,
        0x200000000000000000000000000010000f2492492492ec000000000000080ffedb6db6dc6ea_u512,
    },
    {
        0xff000000000000000000000000000000000000000400000092767600000000000000000000000081000000000000000000000001020000000000eeffffffffff_u512,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000005000000000000000000ffffffffff100000000000000000_u512,
        0x0_u512,
        0xff000000000000000000000000000000000000000400000092767600000000000000000000000081000000000000000000000001020000000000eeffffffffff_u512,
    },
    {
        0xfffffffffffffffffffffffffffffffffffffffbffffff6d8989ffffffffffffffffffffffff7efffffffffffffffffffffffefdffffffffff110000000001_u512,
        0xfffffffffffffffffffffffaffffffffffffffffff0000000000f00000000000000000_u512,
        0x1000000000000000000000004fffffffffffffffc00ffff8689890fff_u512,
        0xffffffec09fffda0afa81efafc00ffff868d481fff71de0d8100efffff110000000001_u512,
    },
    {
        0x767676767676000000000076000000000000005600000000000000000000_u512,
        0x767676767676000000000076000000760000_u512,
        0xffffffffffffffffffffffff_u512,
        0x767676007676005600000076000000760000_u512,
    },
    {
        0x8200000000000000000000000000000000000000000000000000000000000000_u512,
        0x8200000000000000fe000004000000ffff000000fffff700_u512,
        0xfffffffffffffffe_u512,
        0x5fffffbffffff01fd00000700000afffe000001ffffee00_u512,
    },
    {
        0xdac7fff9ffd9e1322626262626262600_u512,
        0xd021262626262626_u512,
        0x10d1a094108c5da55_u512,
        0x6f386ccc73c11f62_u512,
    },
    {
        0x8000000000000001800000000000000080000000000000008000000000000000_u512,
        0x800000000000000080000000000000008000000000000000_u512,
        0x10000000000000001_u512,
        0x7fffffffffffffff80000000000000000000000000000000_u512,
    },
    {
        0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002200000000000000000000000000000000000000000000000000000000000000000000_u512,
        0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002280ff0000000000000000000000000000000000000000000000000000000000000000_u512,
        0,
        0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002200000000000000000000000000000000000000000000000000000000000000000000_u512,
    },
    {
        0x000000c9700000000000000000023f00c00014ff0000000000000000223008050000000000000000000000000000000000000000000000000000000000000000_u512,
        0x00000000c9700000000000000000023f00c00014ff002c0000000000002231080000000000000000000000000000000000000000000000000000000000000000_u512,
        0xff,
        0x00000000c9700000000000000000023f00c00014fed42c00000000000021310d0000000000000000000000000000000000000000000000000000000000000000_u512,
    },
    {
        0x40000000fd000000db00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001_u512,
        0x40000000fd000000db0000000000000000000040000000fd000000db000001_u512,
        0xfffffffffffffffffffffffffffffffffffffeffffffffffffffff_u512,
        0x3ffffffffd000000db000040000000fd0000011b000001fd000000db000002_u512,
    },
    {
        0x40000000fd000000db00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001_u512,
        0x40000000fd000000db0000000000000000000040000000fd000000db0000d3_u256,
        0xfffffffffffffffffffffffffffffffffffffeffffffffffffffff_u256,
        0x3fffff2dfd000000db000040000000fd0000011b0000d3fd000000db0000d4_u256,
    },
    {
        0x001f000000000000000000000000000000200000000100000000000000000000_u256,
        0x0000000000000000000100000000ffffffffffffffff0000000000002e000000_u256,
        0x1effffffe10000001f_u128,
        0xfffa6e20000591fffffa6e000000_u128,
    },
    {
        0x7effffff80000000000000000000000000020000440000000000000000000001_u256,
        0x7effffff800000007effffff800000008000ff0000010000_u256,
        0xfffffffffffffffe,
        0x7effffff800000007e0100ff43ff00010001fe0000020001_u256,
    },
    {
        0x5fd8fffffffffffffffffffffffffffffc090000ce700004d0c9ffffff000001_u256,
        0x2ffffffffffffffffffffffffffffffffff000000030000_u256,
        0x1ff2ffffffffffffff_u256,
        0x2fffffffffffffffc28f300ce102704d0c8ffffff030001_u256,
    },
    {
        0x62d8fffffffffffffffffffffffffffffc18000000000000000000ca00000001_u256,
        0x2ffffffffffffffffffffffffffffffffff200000000000_u256,
        0x20f2ffffffffffffff_u256,
        0x2fffffffffffffffc34d49fffffffffffff20ca00000001_u256,
    },
    {
        0x7effffff8000000000000000000000000000000000000000d900000000000001_u256,
        0x7effffff8000000000000000000000000000000000008001_u256,
        0xffffffffffffffff,
        0x7effffff7fffffffffffffffffff7fffd900000000008002_u256,
    },
    {
        0x0000000000000006400aff20ff00200004e7fd1eff08ffca0afd1eff08ffca0a_u256,
        0x00000000000000210000000000000022_u128,
        0x307c7456554d945ce57749fd52bfdb7f_u128,
        0x1491254b5a0b84a32c_u128,
    },
    {
        0x7effffff8000000000000000000000000000000000150000d900000000000001_u256,
        0x7effffff8000000000000000000000000000000000f9e101_u256,
        0xffffffffffffffff,
        0x7effffff7fffffffffffffffff1b1effd900000000f9e102_u256,
    },
    {
        0xffffffff0100000000000000000000000000ffff0000ffffffff0100000000_u256,
        0xffffffff010000000000000000000000ffff0000ffffff_u256,
        0xffffffffffffffff,
        0xffffffff00ffffff0001fffe00010100fffe0100ffffff_u256,
    },
    {
        0xabfffff0000ffffffffff36363636363636363636d00500000000ffffffffffffe90000ff00000000000000000000ffff0000000000_u512,
        0xabfffff0000ffffffffff36363636363636363636d00500000000ffffffffffffe9ff001f_u512,
        0xffffffffffffffffffffffffffffffffff_u256,
        0xabfffff0000ffffffffff36363636363537371636d00500000001000000fffeffe9ff001f_u512,
    },
    {
        0xff00ffffffffffffffcaffffffff0100_u128,
        0x0100000000000000ff800000000000ff_u128,
        0xff,
        0xffffffffff017f4afffffffe02ff_u128,
    },
    {
        0x9000ffffffffffffffcaffffffff0100_u128,
        0x800000000000007fc000000000007f80_u128,
        1,
        0x1000ffffffffff803fcafffffffe8180_u128,
    },
    {
        // Very special case for reciprocal_3by2().
        uint128{9223374235880128514u, 9223372036855824384u},
        uint128{9223374235880128513u, 9223372036855824384u},
        1,
        1,
    },
    {
        0x6e2d23924d38f0ab643864e9b2a328a54914f48533114fae3475168bfd74a61ae91e676b4a4f33a5b3b6cc189536ccb4afc46d02b061d6daaf0298c993376ab4_u512,
        uint128{9223374235880128513u, 9223372036855824384u},
        0xdc5a47249a56560d078334729ffb61da211f5d2ec622c22f88bc3b4ebae1abdac6b03621554ef71070bc1e0dc5c301bc_u512,
        0x6dc100ea02272bdcf68a4a5b95f468f8_u128,
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

TEST(div, udivrem_384)
{
    for (auto& t : div_test_cases)
    {
        const auto n = static_cast<uint384>(t.numerator);
        const auto d = static_cast<uint384>(t.denominator);
        if (n != t.numerator || d != t.denominator)
            continue;  // Skip trimmed arguments.

        const auto [quot, rem] = udivrem(n, d);
        EXPECT_EQ(quot, t.quotient);
        EXPECT_EQ(rem, t.reminder);
    }
}

TEST(div, udivrem_256)
{
    for (auto& t : div_test_cases)
    {
        const auto n = static_cast<uint256>(t.numerator);
        const auto d = static_cast<uint256>(t.denominator);
        if (n != t.numerator || d != t.denominator)
            continue;  // Skip trimmed arguments.

        const auto [quot, rem] = udivrem(n, d);
        EXPECT_EQ(quot, t.quotient);
        EXPECT_EQ(rem, t.reminder);
    }
}

TEST(div, udivrem_320_by_256)
{
    for (auto& t : div_test_cases)
    {
        const auto n = static_cast<uint320>(t.numerator);
        const auto d = static_cast<uint256>(t.denominator);
        if (n != t.numerator || d != t.denominator)
            continue;  // Skip trimmed arguments.

        const auto [quot, rem] = udivrem(n, d);
        EXPECT_EQ(quot, t.quotient);
        EXPECT_EQ(rem, t.reminder);
    }
}

TEST(div, udivrem_512_by_256)
{
    for (auto& t : div_test_cases)
    {
        const auto d = static_cast<uint256>(t.denominator);
        if (d != t.denominator)
            continue;  // Skip trimmed divisors.

        const auto [quot, rem] = udivrem(t.numerator, d);
        EXPECT_EQ(quot, t.quotient);
        EXPECT_EQ(rem, t.reminder);
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
    }
}

TEST(div, sdivrem_512)
{
    const auto n = 13_u512;
    const auto d = 3_u512;

    EXPECT_EQ(sdivrem(n, d).quot, 4_u512);
    EXPECT_EQ(sdivrem(n, d).rem, 1_u512);
    EXPECT_EQ(sdivrem(-n, -d).quot, 4_u512);
    EXPECT_EQ(sdivrem(-n, -d).rem, -1_u512);
    EXPECT_EQ(sdivrem(-n, d).quot, -4_u512);
    EXPECT_EQ(sdivrem(-n, d).rem, -1_u512);
    EXPECT_EQ(sdivrem(n, -d).quot, -4_u512);
    EXPECT_EQ(sdivrem(n, -d).rem, 1_u512);
}

inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    const auto u = uint128{~uint64_t{0}, ~d};
    uint64_t v{};

#if __x86_64__
    uint64_t _{};
    asm("divq %4" : "=d"(_), "=a"(v) : "d"(u[1]), "a"(u[0]), "g"(d));  // NOLINT(hicpp-no-assembler)
#else
    v = (u / d)[0];
#endif

    return v;
}

TEST(div, reciprocal)
{
    constexpr auto n = 1000000;

    constexpr auto d_start = uint64_t{1} << 63;
    for (uint64_t d = d_start; d < d_start + n; ++d)
    {
        auto v = reciprocal_2by1(d);
        ASSERT_EQ(v, reciprocal_naive(d)) << d;
    }

    constexpr auto d_end = ~uint64_t{0};
    for (uint64_t d = d_end; d > d_end - n; --d)
    {
        auto v = reciprocal_2by1(d);
        ASSERT_EQ(v, reciprocal_naive(d)) << d;
    }
}

TEST(div, reciprocal_3by2)
{
    // Basic inputs for reciprocal_3by2() to make porting to other languages easier.

    EXPECT_EQ(reciprocal_3by2({0x0000000000000000, 0x8000000000000000}), 0xffffffffffffffffu);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000001, 0x8000000000000000}), 0xffffffffffffffffu);
    EXPECT_EQ(reciprocal_3by2({0x8000000000000000, 0x8000000000000000}), 0xfffffffffffffffeu);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000000, 0x8000000000000001}), 0xfffffffffffffffcu);
    EXPECT_EQ(reciprocal_3by2({0xffffffffffffffff, 0x8000000000000000}), 0xfffffffffffffffcu);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000000, 0xc000000000000000}), 0x5555555555555555u);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000001, 0xc000000000000000}), 0x5555555555555555u);
    EXPECT_EQ(reciprocal_3by2({0xffffffffffffffff, 0xc000000000000000}), 0x5555555555555553u);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000000, 0xfffffffffffffffe}), 2u);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000001, 0xfffffffffffffffe}), 2u);
    EXPECT_EQ(reciprocal_3by2({0xffffffffffffffff, 0xfffffffffffffffe}), 1u);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000000, 0xffffffffffffffff}), 1u);
    EXPECT_EQ(reciprocal_3by2({0x0000000000000001, 0xffffffffffffffff}), 0u);
    EXPECT_EQ(reciprocal_3by2({0xffffffffffffffff, 0xffffffffffffffff}), 0u);
}

TEST(div, reciprocal_table)
{
    uint8_t d = 0;
    EXPECT_EQ(internal::reciprocal_table_item(d), 2045);
    d = 0xff;
    EXPECT_EQ(internal::reciprocal_table_item(d), 1024);
}
