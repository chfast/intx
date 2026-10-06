// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <experimental/div.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <test/utils/random.hpp>

using namespace intx;

TEST(div, udivrem_constexpr)
{
    // Two word quotient (3-word divisor) with non-zero and zero normalization shift.
    constexpr auto u = (uint256{0xfedcba9876543210} << 192) | 0x0123456789abcdef;
    constexpr auto v1 = (uint256{0x1234} << 128) | 0x5678;
    constexpr auto v0 = (uint256{0x8000000000000001} << 128) | 0x5678;
    static_assert(udivrem(u, v1).quot * v1 + udivrem(u, v1).rem == u);
    static_assert(udivrem(u, v1).rem < v1);
    static_assert(udivrem(u, v0).quot * v0 + udivrem(u, v0).rem == u);
    static_assert(udivrem(u, v0).rem < v0);

    // Knuth division (uint512, 3-word divisor) with non-zero and zero normalization shift.
    constexpr auto x = (uint512{0xfedcba9876543210} << 448) | 0x0123456789abcdef;
    constexpr auto w1 = (uint512{0x1234} << 128) | 0x5678;
    constexpr auto w0 = (uint512{0x8000000000000001} << 128) | 0x5678;
    static_assert(udivrem(x, w1).quot * w1 + udivrem(x, w1).rem == x);
    static_assert(udivrem(x, w1).rem < w1);
    static_assert(udivrem(x, w0).quot * w0 + udivrem(x, w0).rem == x);
    static_assert(udivrem(x, w0).rem < w0);
}

TEST(div, normalize)
{
    uint512 u;
    uint512 v = 1;
    auto na = internal::normalize(u, v, count_significant_words(v));
    EXPECT_EQ(na.shift, 63u);
    EXPECT_EQ(na.num_divisor_words, 1);
    EXPECT_EQ(na.num_numerator_words, 0);
    EXPECT_EQ(na.numerator, 0);
    EXPECT_EQ(na.divisor, v << 63);

    u = uint512{1313, 0, 0, 0, 1414, 0, 0, 0};
    v = uint512{1212, 0, 0, 0, 12, 0, 0, 0};
    na = internal::normalize(u, v, count_significant_words(v));
    EXPECT_EQ(na.shift, 60u);
    EXPECT_EQ(na.num_divisor_words, 5);
    EXPECT_EQ(na.num_numerator_words, 6);
    EXPECT_EQ(na.numerator, u << 60);
    EXPECT_EQ(na.divisor, v << 60);

    u = uint512{3} << 510;
    v = uint256{1, 0, 0xffffffffffffffff, 0};
    na = internal::normalize(u, v, count_significant_words(v));
    EXPECT_EQ(na.shift, 0u);
    EXPECT_EQ(na.num_divisor_words, 3);
    EXPECT_EQ(na.num_numerator_words, 8);
    EXPECT_EQ(na.numerator, u);
    EXPECT_EQ(na.divisor, v);

    u = uint512{7} << 509;
    v = uint256{1, 0, 0x3fffffffffffffff, 0};
    na = internal::normalize(u, v, count_significant_words(v));
    EXPECT_EQ(na.shift, 2u);
    EXPECT_EQ(na.num_divisor_words, 3);
    EXPECT_EQ(na.num_numerator_words, 9);
    EXPECT_EQ(na.numerator, intx::uint<576>{u} << 2);
    EXPECT_EQ(na.divisor, v << 2);
}

namespace
{
template <typename Int>
struct div_test_case
{
    Int numerator;
    Int denominator;
    Int quotient;
    Int reminder;
};

const div_test_case<uint512> div_test_cases[] = {
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
    // Divisors with the top word not zero, i.e. single word quotients.
    // The "estimate" is the quotient estimated from the top words of the normalized operands.
    // 192-bit: u < v by the top word.
    {
        0xb260f5e964964ec144bcc91741d51805e8eea1e2ed3578a8_u512,
        0xe2dcaa37f463b337d20b5d59db610487c89da11b62397bc7_u512,
        0x0_u512,
        0xb260f5e964964ec144bcc91741d51805e8eea1e2ed3578a8_u512,
    },
    // 192-bit: u < v with equal top words.
    {
        0x62e3fe85351d23832899387134f069bf953a6f229735a0_u512,
        0x62e3fe85351d23832899387134f069bf953a6f229735a1_u512,
        0x0_u512,
        0x62e3fe85351d23832899387134f069bf953a6f229735a0_u512,
    },
    // 192-bit: top bit set, estimate 1 too big.
    {
        0x8ed904759531985d5d9dc9f81818e811892f902bd23f0823_u512,
        0x8ed904759531985d5d9dc9f81818e811892f902bd23f0824_u512,
        0x0_u512,
        0x8ed904759531985d5d9dc9f81818e811892f902bd23f0823_u512,
    },
    // 192-bit: top bit set, exact estimate.
    {
        0xdaee4623d477b79714c8a9893992d5411b90f60d3da1c0ba_u512,
        0xc36a9864fc741d8c339863efcf019ed91ef2be2ab7bbe1d6_u512,
        0x1_u512,
        0x1783adbed8039a0ae13045996a913667fc9e37e285e5dee4_u512,
    },
    // 192-bit: exact estimate.
    {
        0x612e7696a6cecc1b78e510617311d8a3c2ce6f447ed4d57b_u512,
        0x20a61a1e0813e268e1c35de266b09f186c78b56fc8db_u512,
        0x2fa00_u512,
        0xcd942c39c2f48e58aed8d681f150fef2335c2f8f77b_u512,
    },
    // 192-bit: estimate 1 too big.
    {
        0x894ee23e2af8894a1023a69a6d7160205c0425f1d501c168_u512,
        0x430a1f0a396c1bd7e8477ab1538793479_u512,
        0x20c54a5adde5fb82_u512,
        0x377addc94b7d268a501e0e389ebc578f6_u512,
    },
    // 192-bit: estimate 2 too big.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x105c6af0758d5563dab2cd31ee3151288_u512,
        0xfa59f18cc1e434dd_u512,
        0x9bf3f3f74e93b7d087762c18a5eb6097_u512,
    },
    // 192-bit: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x100000000000000000000000000000000_u512,
        0xffffffffffffffff_u512,
        0xffffffffffffffffffffffffffffffff_u512,
    },
    // 256-bit: u < v by the top word.
    {
        0xc858bbc8e29253805a052d8452bbf988c9155952f02595394cad46d34f83258_u512,
        0xbd91a1b7f03edca7e2dcaa37f463b337d20b5d59db610487c89da11b62397bc7_u512,
        0x0_u512,
        0xc858bbc8e29253805a052d8452bbf988c9155952f02595394cad46d34f83258_u512,
    },
    // 256-bit: u < v with equal top words.
    {
        0x1a47e105825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bb_u512,
        0x1a47e105825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bc_u512,
        0x0_u512,
        0x1a47e105825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bb_u512,
    },
    // 256-bit: top bit set, estimate 1 too big.
    {
        0x899950d836f675cc81e74ef5e8e25d940ed904759531985d5d9dc9f81818e810_u512,
        0x899950d836f675cc81e74ef5e8e25d940ed904759531985d5d9dc9f81818e811_u512,
        0x0_u512,
        0x899950d836f675cc81e74ef5e8e25d940ed904759531985d5d9dc9f81818e810_u512,
    },
    // 256-bit: top bit set, exact estimate.
    {
        0xdc6b13ab2e47dc0e959f3a518cfe5cd12d5db79ba2a7ae1f3ac7652ccdf84404_u512,
        0x99901c0475491bc354c56c9a9cc9af4ec9546b439f9d01298a449ebe89d9bf02_u512,
        0x1_u512,
        0x42daf7a6b8fec04b40d9cdb6f034ad8264094c58030aacf5b082c66e441e8502_u512,
    },
    // 256-bit: exact estimate.
    {
        0x1df2dba4c161cabaf9f631798ac493fe940e6988798b0d4262ca097f68951cc4_u512,
        0x3f6a6abd8f17f5c4a0a61a1e0813e268e1c35de266b09f186c78b56fc8db_u512,
        0x78e6_u512,
        0x2_u512,
    },
    // 256-bit: estimate 1 too big.
    {
        0x72a9b8a4c0d76560fbbe938116e3e38047e1a38bd1ea041814d4954e5c47577b_u512,
        0x32ffd03d4eac98d63534ccae8aa672352ee7af97425375be5_u512,
        0x23f9246661a9c53b_u512,
        0x305c6a867bec55f1dc88bc0069cb788d77f085a4abfa0f0b4_u512,
    },
    // 256-bit: estimate 2 too big.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x1076b3e36bb2313f55b06258e7e26f36a8483f8b8332dd331_u512,
        0xf8ca3f4674837868_u512,
        0xd72ecc541106e7f103d78fee414d74aa2e2edaa274503c17_u512,
    },
    // 256-bit: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x1000000000000000000000000000000000000000000000000_u512,
        0xffffffffffffffff_u512,
        0xffffffffffffffffffffffffffffffffffffffffffffffff_u512,
    },
    // 384-bit: u < v by the top word.
    {
        0x67f86286688eed8f5ec1c3d1eefb98a946ac0cee6c1a7ddcade3485d993b27e26e9487c1c77ad8c807c6144875a3ae18_u512,
        0x70fffc69f89d044cc7ecca4e5f9d52853093a9f890f84bb8d24bb46ce859582e75b81ccf813dcbdff9e61f04c4c59129_u512,
        0x0_u512,
        0x67f86286688eed8f5ec1c3d1eefb98a946ac0cee6c1a7ddcade3485d993b27e26e9487c1c77ad8c807c6144875a3ae18_u512,
    },
    // 384-bit: u < v with equal top words.
    {
        0x9531985d5d9dc9f81818e811892f902bd23f0824128b2f330c5c7fd0a6a3a4506513270e269e0d37f2a74de452e6b42_u512,
        0x9531985d5d9dc9f81818e811892f902bd23f0824128b2f330c5c7fd0a6a3a4506513270e269e0d37f2a74de452e6b43_u512,
        0x0_u512,
        0x9531985d5d9dc9f81818e811892f902bd23f0824128b2f330c5c7fd0a6a3a4506513270e269e0d37f2a74de452e6b42_u512,
    },
    // 384-bit: top bit set, estimate 1 too big.
    {
        0xecad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a35a099950d836f675cc81e74ef5e8e25d93_u512,
        0xecad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a35a099950d836f675cc81e74ef5e8e25d94_u512,
        0x0_u512,
        0xecad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a35a099950d836f675cc81e74ef5e8e25d93_u512,
    },
    // 384-bit: top bit set, exact estimate.
    {
        0xc278a62be932c05746514092fcd67dc52c705ab1621b7e461e1ff187fa72ab370c50b95992714cfc65aeb4d48cea1f2e_u512,
        0x81b698ac13cfba03680d5215b6c71cde4d7a663273d455ee2cd84e8187ab701fdbaf86abd786aa76bf8ded91737a6bbf_u512,
        0x1_u512,
        0x40c20d7fd5630653de43ee7d460f60e6def5f47eee472857f147a30672c73b1730a132adbaeaa285a620c743196fb36f_u512,
    },
    // 384-bit: exact estimate.
    {
        0x41c86ba411842d9ebe3618b44cd213073e188514669e9bde07dd425573cafef14d20c14a93928a5b997decca9ce18b2e_u512,
        0x5367660dbc728830b988ec51e16737a23f6a6abd8f17f5c4a0a61a1e0813e268e1c35de266b09f186c78b56fc8db_u512,
        0xc9ea_u512,
        0x0_u512,
    },
    // 384-bit: estimate 1 too big.
    {
        0xfcf1fc03cd04b2823070a5e1a8aca0e3682b5fd037e5e965c5ff47b1d2c844cae97295385daa7f2743d055b7044b14eb_u512,
        0x208fd558642403cb6e76588860a302fb823b4a1ff1b8a06532ae33a73a7997401853148d2c68f8713_u512,
        0x7c4a552f237b9697_u512,
        0x15d6df9d12e0abaefa6471bc2f220c1fc29f0e9660f1a3a02960aa82fafe82d09a8f6bf214d5c46b6_u512,
    },
    // 384-bit: estimate 2 too big.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x106ec41adea0575438b0d590bb0a844e52587be6b5c9bcf35873be078f3b7a50df373ca533488f876_u512,
        0xf942686245892c8b_u512,
        0xe0e4936c0e21a8a5c597937e7ef899ba36fd6d5b025741f286be29c8afc376e89fdfc25a29c6cfed_u512,
    },
    // 384-bit: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x100000000000000000000000000000000000000000000000000000000000000000000000000000000_u512,
        0xffffffffffffffff_u512,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
    },
    // 512-bit: u < v by the top word.
    {
        0xcb14957dce1c61527ace77832dd5ad98475c61b1af3ef55c43ecf2b9fec08e901e5fa037bdba19ebabf100b0d5bc9f746b6cd23aadd763fa8d86850ebc098fd8_u512,
        0xed10e6b8f837a7d6a6ce9740f233f6920c0a78d058c17f6b6c0046f488d4161a37e103558cb252440d05f982feebb948f46ed6dd9ca4f36e6d7cd4ed16d35266_u512,
        0x0_u512,
        0xcb14957dce1c61527ace77832dd5ad98475c61b1af3ef55c43ecf2b9fec08e901e5fa037bdba19ebabf100b0d5bc9f746b6cd23aadd763fa8d86850ebc098fd8_u512,
    },
    // 512-bit: u < v with equal top words.
    {
        0x6deceb9903ce9dfbd1c4bb281db208eb2a6330babb3b93f03031d023125f2057a47e104825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bc8a5cd686_u512,
        0x6deceb9903ce9dfbd1c4bb281db208eb2a6330babb3b93f03031d023125f2057a47e104825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bc8a5cd687_u512,
        0x0_u512,
        0x6deceb9903ce9dfbd1c4bb281db208eb2a6330babb3b93f03031d023125f2057a47e104825165e6618b8ffa14d4748a0ca264e1c4d3c1a6fe54e9bc8a5cd686_u512,
    },
    // 512-bit: top bit set, estimate 1 too big.
    {
        0xa09f76b5a170b33839263059f28c105d1fb17c2390c192cfd3ac94af0f21ddb66cad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a359_u512,
        0xa09f76b5a170b33839263059f28c105d1fb17c2390c192cfd3ac94af0f21ddb66cad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a35a_u512,
        0x0_u512,
        0xa09f76b5a170b33839263059f28c105d1fb17c2390c192cfd3ac94af0f21ddb66cad4a268d116ece1738f7d93d9c172411e20b8f6b0d549b6f03675a1600a359_u512,
    },
    // 512-bit: top bit set, exact estimate.
    {
        0xc81117185b21d0df09736bf82db13b2f8ebf8fcd6026e5a6c815de18f38840c99ace3b175aa959cb710c431a52d63bc50ff6e16be832c17915849b2b31f68e39_u512,
        0x94765878b25f740a9bb9f93bad21e937647faf5b715631350e02d989565843747b36767ee5b3c99aa231286cd47df12fa4ab16ac5a0d6c30774e0fe6f5e4207b_u512,
        0x1_u512,
        0x339abe9fa8c25cd46db972bc808f51f82a3fe071eed0b471ba13048f9d2ffd551f97c49874f59030cedb1aad7e584a956b4bcabf8e2555489e368b443c126dbe_u512,
    },
    // 512-bit: exact estimate.
    {
        0x57320feacf0c4adf29b957d736a99c58b35472afb1b74071a293c32a45ef21c790425ab3c88be5bd15f5898df6a0513d368bef652d4de2af434414d54fc577_u512,
        0xc0397461adfcc96e4f4e30b30973b4b5367660dbc728830b988ec51e16737a23f6a6abd8f17f5c4a0a61a1e0813e268e1c35de266b09f186c78b56fc8db_u512,
        0x742_u512,
        0x1_u512,
    },
    // 512-bit: estimate 1 too big.
    {
        0xc67b3cd813d7c7ef94d441df6e958ed7689a222727caebf48c556d496afa07287f1b840fab03175b7e7e819957da18c180e45876e8f96d77697ac625da70e395_u512,
        0x3590d9fbcb286b8f33c4b4341e65cf5f3fe96f0ea19bbecb28cc0211f1420596217eb678d74d102698b66cc15c739cde60033f97f4179cbe9_u512,
        0x3b4935cf101224dc_u512,
        0x310c00773284353aa471848a6cfa2fe0a9a5c248be12131392ebf9666333496f2f8a81a3594434aacc1de2275521a0c5a6d8c21de8eb6e359_u512,
    },
    // 512-bit: estimate 2 too big.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x12188287e8c5c715f8c74fc1e27e9e06f59b44e92effddeeaa842bc19796f74adfaf55496988af3fbd39630d69c9011ef256badf9a7e6529b_u512,
        0xe25a021b64ba353f_u512,
        0xf81c6278a3583e1403c11984fbe12de9494c4b0ade7c1da0de4f31cc3bd4b39ee63937f6eec95dae74658b21d8c02aaa30139dd76e9994da_u512,
    },
    // 512-bit: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000_u512,
        0xffffffffffffffff_u512,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
    },
    // Divisors with one word less than the numerator, i.e. two word quotients.
    // The "estimate" is the quotient estimated from the top 4 words of the normalized numerator
    // and the top 2 words of the normalized divisor.
    // 256-bit, 3-word divisor: estimate exact, not normalized, quotient < 2^64.
    {
        0x1f43319b8ddf9ccfd8de894c9a2736d4ae4c59fc740cce622_u512,
        0x3911650e9aeb5af8a39ea9ba67c665412_u512,
        0x8c3d5f169293de90_u512,
        0x2_u512,
    },
    // 256-bit, 3-word divisor: estimate exact, not normalized, quotient >= 2^64.
    {
        0xffffffffffffffffc000000000000001fffffffffffffffba4c449881c593af6_u512,
        0x400000000000000000000000000000007fffffffffffffff_u512,
        0x3ffffffffffffffff_u512,
        0x24c449881c593af5_u512,
    },
    // 256-bit, 3-word divisor: estimate exact, top bit set, quotient < 2^64.
    {
        0x720b1903e84a24cb8000000000000000e4163207d0944996996d3c6fded38aca_u512,
        0x80000000000000000000000000000000ffffffffffffffff_u512,
        0xe4163207d0944997_u512,
        0x7d836e77af67d461_u512,
    },
    // 256-bit, 3-word divisor: estimate exact, top bit set, quotient >= 2^64.
    {
        0xfffffffffffffffd0000000000000001fffffffffffffff85b4c8012ede7bd12_u512,
        0x80000000000000000000000000000000ffffffffffffffff_u512,
        0x1fffffffffffffffa_u512,
        0x5b4c8012ede7bd0c_u512,
    },
    // 256-bit, 3-word divisor: estimate 1 too big, not normalized, quotient < 2^64.
    {
        0x51c130321b48292a7868003552a41c81e46685b06f421a688a5ac1d1ee893e79_u512,
        0x5d46d320a4d023ee25643fe044df4e0e475a8a078b7a2440_u512,
        0xe060a72424114259_u512,
        0x5d46d320a4d023ee25643fe044df4e0e475a8a078b7a2439_u512,
    },
    // 256-bit, 3-word divisor: estimate 1 too big, not normalized, quotient >= 2^64.
    {
        0xffffffffe684bc870000000000000001ffffffffcd09790a0000000065ed0d0b_u512,
        0x400000000000000000000000000000007fffffffffffffff_u512,
        0x3ffffffff9a12f21b_u512,
        0x400000000000000000000000000000007fffffffffffff26_u512,
    },
    // 256-bit, 3-word divisor: estimate 1 too big, top bit set, quotient < 2^64.
    {
        0x1d77edc9d98a3a3d893b3e3c44d6f0ea4db18077a8451e7fc68589dc6caaf7bd_u512,
        0x833f867ece1fd3d9849acfb58350a73fffffffffffffffff_u512,
        0x397a762393550841_u512,
        0x833f867ece1fd3d9849acfb58350a73ffffffffffffffffe_u512,
    },
    // 256-bit, 3-word divisor: estimate 1 too big, top bit set, quotient >= 2^64.
    {
        0xffffffff9e64bac460b66c5a1ea9fa734318ec426d459817eeb9469af88f321f_u512,
        0xcfa7d815b7a1774f1a42721eaba4c70ee306f0c485f184e0_u512,
        0x13b9973a32a8f8786_u512,
        0xcfa7d815b7a1774f1a42721eaba4c70ee306f0c485f184df_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate exact, not normalized, quotient < 2^64.
    {
        0x7f28470d1a0153947c5aff26ad7b9a14e0434605decebbce7bace2ca8b48c7d0_u512,
        0x1fa97002df975a2cfeb5394bfdbe2cbb56dd5ffeaf055fcd7_u512,
        0x4041f5ee8bae8e67_u512,
        0x166eebc578f4ecb4f_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate exact, not normalized, quotient >= 2^64.
    {
        0xfffffffffffffffc8000000000000001fffffffffffffff9132e14750879d951025ff87c44df8a21_u512,
        0x400000000000000000000000000000007fffffffffffffffffffffffffffffff_u512,
        0x3fffffffffffffff2_u512,
        0x132e14750879d955025ff87c44df8a13_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate exact, top bit set, quotient < 2^64.
    {
        0x613805871014b58decc72e0c89099eb5bd617165bd1f85ba511070a74a41f8e451f4715491248acd_u512,
        0xbe272124b1515fff42969a5033288e16ffffffffffffffffffffffffffffffff_u512,
        0x82e261237776c656_u512,
        0x511070a74a41f8e4d4d6d278089b5123_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate exact, top bit set, quotient >= 2^64.
    {
        0xffffffff6b71491f81d259f6c36088b0e0bac9f63d2a404b6cffb0f0f79edc8098224d42c95f4608_u512,
        0xa121611283e2665af6540600c8fb4456ffffffffffffffffffffffffffffffff_u512,
        0x196b9fc7f2dbc8b2d_u512,
        0x6cffb0f0f79edc822edc49c1f71bd135_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate 1 too big, not normalized, quotient < 2^64.
    {
        0x289751a3dba8375c56ce18730d1fbcc6238d7ed580a48bc0411dc4d9fb764dfca70796db36831b5d_u512,
        0x5a52eab5eda64a495fafc2f118e836ce0c5f703a2f6061303fcc4053739e24f5_u512,
        0x730b89dc2577c325_u512,
        0x5a52eab5eda64a495fafc2f118e836ce0c5f703a2f6061303fcc4053739e24f4_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate 1 too big, not normalized, quotient >= 2^64.
    {
        0xfffffffffffffffffffffffe9ed83899ffffffffffffffff7ffffffd3db0713000000000b093e3b3_u512,
        0x200000000000000000000000000000003ffffffffffffffff_u512,
        0x7fffffffffffffffffffffff4f6c1c4b_u512,
        0x200000000000000000000000000000003fffffffffffffffe_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate 1 too big, top bit set, quotient < 2^64.
    {
        0x7aa8d5fe90cbb1e38000000000000000f551abfd219763c6ffffffffffffffff0aae5402de689c23_u512,
        0x80000000000000000000000000000000ffffffffffffffffffffffffffffffff_u512,
        0xf551abfd219763c6_u512,
        0x80000000000000000000000000000000ffffffffffffffffffffffffffffffe9_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate 1 too big, top bit set, quotient >= 2^64.
    {
        0xffffffffb4a82bb5acafb4ecf22aa4fb529e379ce8da98e3fffffffffffffffeac690ada46dad7f2_u512,
        0xc0fc60254e564cbf96060250ea3e7f73ffffffffffffffffffffffffffffffff_u512,
        0x15396f525b925280c_u512,
        0xc0fc60254e564cbf96060250ea3e7f73fffffffffffffffffffffffffffffffe_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: estimate 2 too big, not normalized, quotient >= 2^64.
    {
        0xffffffffffffffffffffffff7aaa72e8109055ea0b4de0be2d74eb3fb1f9146e72f04cefcc8f8f01_u512,
        0x15b20f1e640aa1b732800484ed97b76e3ffffffffffffffff_u512,
        0xbccb66ae048a00d8c6407af5f62d48e1_u512,
        0x15b20f1e640aa1b732800484ed97b76e33930c7e5c2bcd7e2_u512,
    },
    // 256-bit, 3-word divisor: u < v.
    {
        0xafa927e2367467387e9b56d2f7c988046f3df106e94a_u512,
        0xafa927e2367467387e9b56d2f7ca1132a960199b3982_u512,
        0x0_u512,
        0xafa927e2367467387e9b56d2f7c988046f3df106e94a_u512,
    },
    // 256-bit, 3-word divisor: zero remainder.
    {
        0x6bbb5310cfa2a336491524184459ed5f4af73f5ffb17f8d0b1a0f3443792dbe0_u512,
        0xae7d0c31db2dcfad759a5eb16c555cbdb8_u512,
        0x9e0ee2f7eb0fdb358ce418b47da864_u512,
        0x0_u512,
    },
    // 256-bit, 3-word divisor: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x1bd328e8a6c0f3455cb3aead1c1e64483_u512,
        0x9334e27de3e38814a87d9c2628bc32f1_u512,
        0x10dcf197fb1a71ba86d709968b4a3eaac_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: u < v.
    {
        0x6c06bb7f4fa3c49356ea3283db7ec7112d4dc1628a16b9c4bc5fb5009e140_u512,
        0x6c06bb7f4fa3c49356ea3283db7ec7112d4dc1628a16bb9c60c657880ed44_u512,
        0x0_u512,
        0x6c06bb7f4fa3c49356ea3283db7ec7112d4dc1628a16b9c4bc5fb5009e140_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: zero remainder.
    {
        0x91d4f841fedd9d1d0aad43da4376fba36b12abe18e43637e676861ce533d807be2006d505b48bfd0_u512,
        0xfdd43013f73f7c61f2b05206e6445bb03075ea816eff8cefa41f7aab341d0_u512,
        0x93144cb95a7ca197161_u512,
        0x0_u512,
    },
    // 320-bit by 256-bit, 4-word divisor: max quotient.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x124dcac35962f8e7e37055de446a10d6bffffffffffffffff_u512,
        0xdfc71a9e4169d4b760bcb64dc82588d6_u512,
        0x892b6f334849dcc104f17f06570b3c6f60bcb64dc82588d5_u512,
    },
    // 384-bit, 5-word divisor: estimate 2 too big, not normalized, max numerator.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x1137ab187ec65205deb71b04a32d451959c3cd4a24d0f1629f8b89f18b8af879f_u512,
        0xede5eb0289324544b53a654ff657b366_u512,
        0xcf798469b01e40a15aa182a3b59954e1576ee12ed211355b98a04df8cd32c9a5_u512,
    },
    // 512-bit, 7-word divisor: estimate 2 too big, not normalized, max numerator.
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u512,
        0x119c8a24333f250a0c9e40bf12b3fe18565edaaef0eecbd2c3b951cb2bdead62c7b3b94bbf2c0d3ce4ab4705b64908af0_u512,
        0xe8935612a516f6029d059e7982a7681f_u512,
        0x1073ba611d1cb8fa852e0d25c057f598740007aa6243fc5c4febd9bec8a7d1a638f12e8091cbd59bc4d0f77cb977dacef_u512,
    },
};
}  // namespace

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

TEST(div, udivrem_192)
{
    for (auto& t : div_test_cases)
    {
        const auto n = static_cast<intx::uint<192>>(t.numerator);
        const auto d = static_cast<intx::uint<192>>(t.denominator);
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

TEST(div, udivrem_320_by_128)
{
    for (auto& t : div_test_cases)
    {
        const auto n = static_cast<uint320>(t.numerator);
        const auto d = static_cast<uint128>(t.denominator);
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


constexpr div_test_case<uint256> sdivrem_test_cases[] = {
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

namespace
{
void check_reciprocal(uint64_t d)
{
    const auto expected = reciprocal_naive(d);
    ASSERT_EQ(reciprocal_2by1(d), expected) << d;
    ASSERT_EQ(reciprocal_native(d), expected) << d;
    ASSERT_EQ(reciprocal_builtin_uint128(d), expected) << d;
    ASSERT_EQ(reciprocal_udiv(d), expected) << d;
}
}  // namespace

TEST(div, reciprocal)
{
    static_assert(reciprocal_2by1(0x8000000000000000) == 0xffffffffffffffff);

    constexpr auto n = 1000000;

    constexpr auto d_start = uint64_t{1} << 63;
    for (uint64_t d = d_start; d < d_start + n; ++d)
        ASSERT_NO_FATAL_FAILURE(check_reciprocal(d));

    constexpr auto d_end = ~uint64_t{0};
    for (uint64_t d = d_end; d > d_end - n; --d)
        ASSERT_NO_FATAL_FAILURE(check_reciprocal(d));

    test::lcg<uint64_t> rng{test::get_seed()};
    for (int i = 0; i < n; ++i)
        ASSERT_NO_FATAL_FAILURE(check_reciprocal(rng() | d_start));
}

TEST(div, reciprocal_3by2)
{
    // Basic inputs for reciprocal_3by2() to make porting to other languages easier.
    static_assert(reciprocal_3by2(0x80000000000000000000000000000000_u128) == 0xffffffffffffffff);

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
    EXPECT_EQ(internal::reciprocal_table[0], 2045);
    EXPECT_EQ(internal::reciprocal_table[0xff], 1024);
}

TEST(div, by128)
{
    // This udivrem() was causing Clang and GCC analyzer failures during compilation
    // of the division dead branch (divisor words > 2).
    const auto x = uint320{1};
    const auto y = uint128{2};
    EXPECT_EQ(udivrem(x, y).rem, 1);
}
