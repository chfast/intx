// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../experimental/addmod.hpp"
#include "test_cases.hpp"
#include <gtest/gtest.h>

using namespace intx;

constexpr uint64_t minimal[] = {
    0x0000000000000000,
    0x0000000000000001,
    0x5555555555555555,
    0x7fffffffffffffff,
    0x8000000000000000,
    0xaaaaaaaaaaaaaaaa,
    0xfffffffffffffffe,
    0xffffffffffffffff,
};

class Uint256Test : public testing::Test
{
protected:
    std::vector<uint256> numbers;

    Uint256Test()
    {
        const auto& parts_set = minimal;
        for (auto a : parts_set)
        {
            for (auto b : parts_set)
            {
                for (auto c : parts_set)
                {
                    for (auto d : parts_set)
                        numbers.emplace_back(d, c, b, a);
                }
            }
        }
    }
};

TEST_F(Uint256Test, add_against_sub)
{
    const auto n = numbers.size();
    for (size_t i = 0; i < n; ++i)
    {
        auto a = numbers[i];
        auto b = numbers[n - 1 - i];
        EXPECT_EQ(a, (a + b) - b);
    }
}

TEST_F(Uint256Test, string_conversions)
{
    for (auto n : numbers)
    {
        auto s = to_string(n);
        auto v = from_string<uint256>(s);
        EXPECT_EQ(n, v);
    }
}

TEST_F(Uint256Test, mul_against_add)
{
    for (auto factor : {0, 1, 3, 19, 32})
    {
        for (auto a : numbers)
        {
            auto s = uint256{0};
            for (int i = 0; i < factor; ++i)
                s += a;

            EXPECT_EQ(a * factor, s);
        }
    }
}

TEST(uint256, simple_udiv)
{
    const char* data_set[][4] = {
        {"85171522646011351805059701872822457992110823852603410913834565603426987238690",
            "3417151701427854447", "24924712183665270310773198889627251242355172875064429410821",
            "3066111968632467703"},
        {"42429462377568411210060890623633389837910568534950317291651048757561669458086",
            "7143279538687112481018702353923999316900435882171572239553505938008016523868", "5",
            "6713064684132848804967378854013393253408389124092456093883519067521586838746"},
        {"51944969322778123844493301323979731028491878961505469250051328399321622613545",
            "16442292418272115516", "3159229139183312667023399387580659588781817989553028093847",
            "4502998155949783493"},
        {"36893488147419103231", "36893488147419103231", "1", "0"},
        {"39614081294025656944191078399", "19342813113834066526863360", "2048",
            "36893488697174917119"},
        {"57896044618658097711785492504343953925954427598978405092802042789093028397056",
            "4184734490257787176003953737778757098546805126749757636608", "13835058055282163711",
            "2615459056411116984492047535730315491393232528557125664768"},
        {"12345678901234567890123456789012345678901234567890123456789012345678901234567",
            "56565656", "218253968472222224208333353174801785714307539682561507936706547621031",
            "43323231"},
        {"9813564515590581114928356250914803191147154229112146631813240906425389644712",
            "203321047708396209413466481480208389591", "48266348350049972453284846493339986789",
            "190176170282161844008482834634484531413"},
        {"8589934592", "1", "8589934592", "0"}};

    for (size_t i = 0; i < sizeof(data_set) / sizeof(data_set[0]); ++i)
    {
        const auto& data = data_set[i];
        const auto n = from_string<uint256>(data[0]);
        const auto d = from_string<uint256>(data[1]);
        const auto expected_q = from_string<uint256>(data[2]);
        const auto expected_r = from_string<uint256>(data[3]);

        const auto res = udivrem(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;
    }
}

TEST(uint256, to_string_chunks)
{
    // Decimal: 19 digits per chunk, divided by 10^19.
    constexpr auto e19 = uint256{10000000000000000000u};
    EXPECT_EQ(to_string(uint256{1} << 64), "18446744073709551616");
    EXPECT_EQ(to_string(e19), "10000000000000000000");
    EXPECT_EQ(to_string(e19 * e19 + 1), "100000000000000000000000000000000000001");
    EXPECT_EQ(to_string(~uint256{0}),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935");

    // Base 36: the divisor 36^12 is not normalized, unlike 10^19.
    EXPECT_EQ(to_string(~uint256{0}, 36), "6dp5qcb22im238nr3wvp0ic7q99w035jmy2iw7i6n43d37jtof");
}

TEST(uint512, literal)
{
    auto x = 1_u512;
    static_assert(std::is_same_v<decltype(x), uint512>);
    EXPECT_EQ(x, 1);

    x = 0_u512;
    EXPECT_EQ(x, 0);

    x = 0xab_u512;
    EXPECT_EQ(x, 0xab);

    x = 0xab12ff00_u512;
    EXPECT_EQ(x, 0xab12ff00);
}

TEST(uint256, arithmetic)
{
    for (const auto& t : arithmetic_test_cases)
    {
        EXPECT_EQ(t.x + t.y, t.sum);
        EXPECT_EQ(t.y + t.x, t.sum);
        EXPECT_EQ(t.sum - t.x, t.y);
        EXPECT_EQ(t.sum - t.y, t.x);
        EXPECT_EQ(t.sum + -t.x, t.y);
        EXPECT_EQ(t.sum + -t.y, t.x);
        EXPECT_EQ(t.x * t.y, t.product);
        EXPECT_EQ(t.y * t.x, t.product);
    }
}

TEST(uint256, exp)
{
    EXPECT_EQ(exp(2_u256, 0_u256), 1);
    EXPECT_EQ(exp(2_u256, 1_u256), 2);
    EXPECT_EQ(exp(2_u256, 2_u256), 4);
    EXPECT_EQ(exp(2_u256, 10_u256), 1024);
    EXPECT_EQ(exp(2_u256, 255_u256),
        0x8000000000000000000000000000000000000000000000000000000000000000_u256);
    EXPECT_EQ(exp(2_u256, 256_u256), 0);

    EXPECT_EQ(exp(3_u256, 0_u256), 1);
    EXPECT_EQ(exp(3_u256, 1_u256), 3);
    EXPECT_EQ(exp(3_u256, 2_u256), 9);
    EXPECT_EQ(exp(3_u256, 20181229_u256),
        83674153047243082998136072363356897816464308069321161820168341056719375264851_u256);
    // The max exponent: 3^(2^256 - 1) is the inverse of 3 mod 2^256.
    EXPECT_EQ(exp(3_u256, ~0_u256),
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab_u256);
}

constexpr decltype(&addmod) addmod_impls[] = {
    addmod,
    test::addmod_public,
    test::addmod_simple,
    test::addmod_prenormalize,
    test::addmod_daosvik_v1,
    test::addmod_daosvik_v2,
};

TEST(uint256, addmod)
{
    static_assert(
        addmod(0xdce049946eccbbf77ed1e8e2a3c89e15a8e897df2194150700f5096dea864cdb_u256,
            0x397dd0df188eaffbf5216c6be56fe49002fbdc23b95a58a60f69e56f6f87f424_u256,
            0xf0f9d0006f7b450e8f73f621a6ca3b56_u128) == 0x7533da49e8c499530049fbf08733976b_u128);

    for (auto&& impl : addmod_impls)
    {
        const auto x = 0xab0f4afc4c78548d4c30e1ab3449e3_u128;
        const auto y = 0xf0a4485af15508e448cdddb0d1301664_u128;
        const auto mod = 0xf0f9d0006f7b450e8f73f621a6ca3b56_u128;
        EXPECT_EQ(impl(x, y, mod), 0x5587a57e263c2a46a61870d59a24f1_u128);
        const auto a = 0xdce049946eccbbf77ed1e8e2a3c89e15a8e897df2194150700f5096dea864cdb_u256;
        const auto b = 0x397dd0df188eaffbf5216c6be56fe49002fbdc23b95a58a60f69e56f6f87f424_u256;
        EXPECT_EQ(impl(a, b, mod), 0x7533da49e8c499530049fbf08733976b_u128);
        // Arguments of at least 2 * mod.
        const auto c = 1_u256 << 255;
        const auto m = (1_u256 << 192) + 1;
        EXPECT_EQ(impl(c, 0, m), 0xffffffffffffffffffffffffffffffff8000000000000001_u256);
        EXPECT_EQ(impl(0, c, m), 0xffffffffffffffffffffffffffffffff8000000000000001_u256);
        EXPECT_EQ(impl(100, 0, 7), 2);
    }
}

TEST(uint256, addmod_ec1)
{
    const auto x = 0x3bc8be7c7deebfbf00000000020000000100_u256;
    const auto y = 0x100000000000000000000000000000000000001000000000000_u256;
    const auto mod = 0x10000000000000000000000000000000000002b000000000000_u256;
    for (auto&& impl : addmod_impls)
        EXPECT_EQ(impl(x, y, mod), 0x3bc8be7c7deebfbeffffffd6020000000100_u256);
}

TEST(uint256, addmod_ec2)
{
    const auto x = 0xffffffffffffffffffffffffffff000004020041fffffffffc00000060000020_u256;
    const auto y = 0xffffffffffffffffffffffffffffffe6000000ffffffe60000febebeffffffff_u256;
    const auto mod = 0xffffffffffffffffffe6000000ffffffe60000febebeffffffffffffffffffff_u256;
    for (auto&& impl : addmod_impls)
        EXPECT_EQ(impl(x, y, mod), 0x33fffffdfeffe63801ff448281e5fffcfebebf60000021_u256);
}

TEST(uint256, mulmod)
{
    static_assert(
        mulmod(0x4028c97ce32bf74a3a3137956b07a5a699ca8422bdf672f547_u256,
            0x8c9f09b6227ba6542a97343c679e1d11d8bfa29228c18615c2_u256,
            0xf0f9d0006f7b450e8f73f621a6ca3b56_u128) == 0xca283039a2ad0dbd3d60fbadb29e9c7a_u128);

    const auto x = 0xab0f4afc4c78548d4c30e1ab3449e3_u128;
    const auto y = 0xf0a4485af15508e448cdddb0d1301664_u128;
    const auto mod = 0xf0f9d0006f7b450e8f73f621a6ca3b56_u128;
    EXPECT_EQ(mulmod(x, y, mod), 0x6c5c6c6fb72967583930f380c2a5269c_u128);
    const auto a = 0x4028c97ce32bf74a3a3137956b07a5a699ca8422bdf672f547_u256;
    const auto b = 0x8c9f09b6227ba6542a97343c679e1d11d8bfa29228c18615c2_u256;
    EXPECT_EQ(mulmod(a, b, mod), 0xca283039a2ad0dbd3d60fbadb29e9c7a_u128);
}

struct mulmod_test_case
{
    uint256 x;
    uint256 y;
    uint256 m;
    uint256 r;
};

// The paths of mulmod() for 1- to 4-word moduli: the normalization shift 0 or not, a power of 2,
// the estimate of q exact or 1 or 2 too large, the Barrett estimate qh >= B or not, the final
// subtraction of d or not.
constexpr mulmod_test_case mulmod_test_cases[] = {
    // 1 word, a power of 2
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3a0_u256,
        0x37ce42c8218072e8c35bf992dc9e9c616612e7696a6cecc1b78e51061_u256,
        0x1_u256,
        0x0_u256,
    },
    // 1 word
    {
        0x8c7e134f5dfbd3d12c4a3698aa2ca1af6a107b75677f6cbdcc22af58be6521cc_u256,
        0x100000000000_u256,
        0xf_u256,
        0x5_u256,
    },
    // 1 word, subtract d
    {
        0x4000000000000000000000_u256,
        0x200000000000000000000000000_u256,
        0x46ac00882accce8_u256,
        0x77897118fe29c0_u256,
    },
    // 1 word, qh >= B
    {
        0xe5f8cec70e93acbf3669ae0ec129fbe4835198854ab80cb9a8e518016a0bf8a0_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffbc094b6a05_u256,
        0x819_u256,
        0x5c1_u256,
    },
    // 1 word, qh >= B, subtract d
    {
        0x2ebe78a19704164195cd9c5a4bb33fcc749e828f701eaefdb4c5ff9abec2cfc2_u256,
        0x800000000000000000000000000000000000000000000000000_u256,
        0x44_u256,
        0x14_u256,
    },
    // 1 word, s = 0
    {
        0x7adb80599e9090b20bb_u256,
        0x3879399bd50e00978b7199cd6d39eb43ad9cedde819d7ca7b46108cc721754ef_u256,
        0x8249627a39b21c95_u256,
        0x20c6729d57569fb7_u256,
    },
    // 1 word, s = 0, subtract d
    {
        0x20000_u256,
        0x10000000000000000000000000000000000000000000000000000000000000_u256,
        0xa13afc0c9df0a140_u256,
        0xb8f29bfd0a37d00_u256,
    },
    // 1 word, s = 0, qh >= B
    {
        0x179c6a8af61d1a64c8ca126f9d2fe537_u256,
        0x94f8811121d6483067e780b094a019f38de2cb2b216820cbb7be18223747c8b7_u256,
        0x816e92154dcc9a93_u256,
        0x5de38ce8fa1f170c_u256,
    },
    // 1 word, s = 0, qh >= B, subtract d
    {
        0x8afe559452cff6604b02847406724ed85f2f0296dff30e1d7db227f27e8af678_u256,
        0x8000000000000000000000000000_u256,
        0x8fe2244c3e33005f_u256,
        0x45e6add38381fca_u256,
    },
    // 1 word, subtract d from R >= B^1
    {
        0x2795bb6577be9de256bcba00e03b6be0ef93e60bb45263c8199301_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd_u256,
        0xea89ab2f605e9a4_u256,
        0x19f94f22af072c5_u256,
    },
    // 1 word, R - qh * d == d
    {
        0x3a5163f4b7728bf865b1d2302cb9e2bbf3fdfbe3d57715f1a1b0b3a8621bed79_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaa15_u256,
        0x3_u256,
        0x0_u256,
    },
    // 2 words, a power of 2
    {
        0x13bef2350b21fbac78255d6807923986bb968a437d5c8dfc_u256,
        0x3a18908092b4d42b28fef0_u256,
        0x20000000000000000000000_u256,
        0x3e6cbe091d7ca6df052440_u256,
    },
    // 2 words
    {
        0x200000000000000000000_u256,
        0x2a4926f05f221dfc8d64b3add9577b6b4cb05ec1b14b69dc4c78c7ab4fd24206_u256,
        0x18ad5251251310bebee3521_u256,
        0x11ab62cba9c2ec3e21dcd8f_u256,
    },
    // 2 words, q estimate 1 too large, subtract d
    {
        0x6839eb905b6e6e307d4bedc51431193e6c3f3391a2b8f1ff1fd42a29755d4c1_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffff3cd2cc61e677526_u256,
        0x1442e3d437204e52d_u256,
        0xdaf740355620d6e_u256,
    },
    // 2 words, q estimate 2 too large, qh >= B
    {
        0x8000000000000000000000000000000_u256,
        0x80000000000000000000000000000000000000000000000000_u256,
        0x40a233735e9f5134e551_u256,
        0x23eec37d330070dd3153_u256,
    },
    // 2 words, qh >= B, subtract d
    {
        0x9857c1fdf0139d41ba8be284ea181662996d98094856551310ae18f8a9c0a4b0_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd573_u256,
        0x14d7dc9a1636be60a_u256,
        0x55ecd251ef4fde5e_u256,
    },
    // 2 words, s = 0, q estimate 1 too large
    {
        0x2a3d9f0d57a92bdf9a0375703241a461a7eece16a4d1931470f5cdfd164ab910_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffebc5_u256,
        0x9e609a169c14ef2eb232e727ad8fbba2_u256,
        0x5a7456f9610ae98c0a72b09c7cf0f2ec_u256,
    },
    // 2 words, s = 0, q estimate 2 too large, subtract d
    {
        0x800000000000000000000000000000000000_u256,
        0x1a1a166e1ce24cbbbb0be1c720a4f74d4a75ecd5bc029c6b1744d89fc537bf7c_u256,
        0x8725349a7a443bd3c9f804504331e8af_u256,
        0xa8b2a56071c565d14742f2e7559c30_u256,
    },
    // 2 words, s = 0, qh >= B
    {
        0x2000000000000000000000000000000000000000000000000_u256,
        0xbea445704cba24fb3ef3de67c0aaccfaa53b83750365cb5cc82d55a2688b26c8_u256,
        0x825fdee350ac638915969089d71099e3_u256,
        0x571126f2bba78f91e07f7427663a93e0_u256,
    },
    // 2 words, s = 0, q estimate 1 too large, qh >= B, subtract d
    {
        0xe372e011cf6031126ab67c6a8bf7f8dd9ff482303a69dc_u256,
        0x400000000000000000000000000000000000_u256,
        0x81e00f8c867cdc6c6d9bd277ba9b1a0e_u256,
        0xc69713d97d467ba43a54717229ee7a6_u256,
    },
    // 2 words, subtract d from R >= B^2
    {
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff742_u256,
        0x420a562244a99c9af240a488a1d16d7a020712c2977e3121aa863f88e2878da8_u256,
        0x1c97e4c0f193276a6_u256,
        0x39073b8ad241b98c_u256,
    },
    // 3 words, a power of 2
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc69b7e63_u256,
        0x80000000000000_u256,
        0x200000000000000000000000000000000000000000_u256,
        0x1fffffffffffffffffffe34dbf3180000000000000_u256,
    },
    // 3 words
    {
        0x80000000000000000000000000000000000000000000000000000000000_u256,
        0x4_u256,
        0x19e296a85804f92283868a29d8f33418f3d4e711_u256,
        0x17ae0bc47aaadc410fd42429f4f5e504aad01899_u256,
    },
    // 3 words, q estimate 1 too large, subtract d
    {
        0x1000000_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffff5f8570fd4fbdf1_u256,
        0x13e89f1b11eba6fdb2439d24ad4402dc9c5975c82a_u256,
        0x18c32554ef1410594cecba9ff1224741b01747758_u256,
    },
    // 3 words, q estimate 2 too large, qh >= B
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff53a191_u256,
        0x400000000000000000000000000000000000000_u256,
        0x102c57f8d5f17fba5940ca29b7f94357a_u256,
        0xf2d699510cf851fec5b725f9c119a3f4_u256,
    },
    // 3 words, qh >= B, subtract d
    {
        0x2dde0aad096a2945a4a5a73c9b7ac81da9eb4691da85df15e5f3624fa44b0b4c_u256,
        0x4000000000000000000000000000000000000000000000000_u256,
        0x8bc1ba0111f1d4e417d28e92fa695ab53097_u256,
        0x27dc37ef0effe754b4b14fc07bce8fa90b65_u256,
    },
    // 3 words, s = 0, q estimate 1 too large
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffd80a4ac2_u256,
        0x20000000000000000000000000000000000000_u256,
        0xd7a4d89c7a44115ae607ca41bb75fccdc811a9bbee031eb1_u256,
        0x6a25be100e9460ba6de7569784628288788251c0b052096c_u256,
    },
    // 3 words, s = 0, q estimate 2 too large, subtract d
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff88b9_u256,
        0x918bedaf595c2c4fd1b3e2f1bbe3f7440626ef9d39c55c59_u256,
        0x2807c84ec363a95fef83871e3541865a5e4a199383ef696e_u256,
    },
    // 3 words, s = 0, qh >= B
    {
        0x146a75a32e0541ae1f75dc690344f0f16e6362b0081d00c175384cc9eec0a374_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffd4fc9f478b2a4_u256,
        0x920e3a6d4ccececc0183a8558bf9765da9a3cfa8b0011e94_u256,
        0x7ab76c1bbc11d8743eaf3d3fbc62a5ceaa4cb130e059ab70_u256,
    },
    // 3 words, s = 0, q estimate 1 too large, qh >= B, subtract d
    {
        0x1927ebad3fe12bbf98f00e49b720e935b085ec78f91d36573559b94a2a9f41f_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9702b_u256,
        0x8464fee9497ff6723454531e7025228ebfc99470589353b4_u256,
        0x46c79428b8fbc6f67c09ab80351162a9125a42b2760c621_u256,
    },
    // 3 words, subtract d from R >= B^3
    {
        0x2e6066397333c20877d11b223ff8bf20cdaf2ddc217f_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff992_u256,
        0x1d1c48b817e7c06ba1252bb97abe39482_u256,
        0x3ecf7b86f812af1242e871fffc114ce0_u256,
    },
    // 4 words, a power of 2
    {
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff22e3ae079_u256,
        0xdeb0e0de26e655d3f21dcc_u256,
        0x1000000000000000000000000000000000000000000000000000000000000_u256,
        0xfffffffffffffffffffffffffffff3fa8ab398c3162d0e37dd126fba956c_u256,
    },
    // 4 words
    {
        0x1000000000000000000000000000000000000000000000000000000_u256,
        0xf0dfb4a5d8a064df7fd63116e1ea24c4f9341c68966baea148beab134da98f1d_u256,
        0x1fe175330a11d459adc2574bdb94067ed1ef2a4f04be03db0_u256,
        0x183c0fa0a6e6b39439e6e90cabb7a055f697d80587cc7b70_u256,
    },
    // 4 words, q estimate 1 too large, subtract d
    {
        0x5297e434377db6e8e543b4a704221bc49ba0638fb7ddd70a93589096c46_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffe98f1fdb436ea7e_u256,
        0x1a2f95494b08647caa9a4a8a0616baa2dc999fc8c08f608be_u256,
        0x281437caa33be81df0a135108437cf9ad078e242e7cb8bc4_u256,
    },
    // 4 words, q estimate 2 too large, qh >= B
    {
        0x400000000000000000000000000000000_u256,
        0xd9e92f07f643306d5f9e9c658ce15e32e9a166f02ab569f9e90d4a6c36a3be8b_u256,
        0x41f079112eb7e41fd42d95f77269c949882e75537b7238671_u256,
        0x3844466303429274d1c0ddc4a34699b27c982cac1ce7ffbba_u256,
    },
    // 4 words, qh >= B, subtract d
    {
        0x2752bfd6cf123784f9a3e9ec36cfc24aa27a402cf11f0_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffff7031f420f8d8_u256,
        0x109955631b0d919f8061b7633ac52b7aac9d159ab4c4eaee8f0b_u256,
        0x511db5c8fd855e37e41807cc742c4e3176208c6c74fbc0172c2_u256,
    },
    // 4 words, s = 0, q estimate 1 too large
    {
        0x4ded5faa9ae0e1b9469a8a20b05c4a59a2cf179f66e4792717d259adb0c12c60_u256,
        0x132ba600118cc43e44e1b856557d728ce2d28da83cbb5615352c5f80873116f0_u256,
        0x88936b8d5aece68f714699bda826e5f12a04ff67050dc58cb5d28dee81d57930_u256,
        0x848d123c1d158f468b54b6c36cc7447d6464bc2757b22af8424ee1cb5d37c7f0_u256,
    },
    // 4 words, s = 0, q estimate 2 too large, subtract d
    {
        0x497c80d8128c5ef76d3594619388aa22eec29bc44fa029d6d3df607b424bdf01_u256,
        0x170cf32a576737d3d8f27b4d7ea889c4c59_u256,
        0x8be80e6e2b69e469eae1ce756f7a1a828eafda7bbab949d634af8363cc12349a_u256,
        0x340a6acbe551f253a1fa3eddff2a4fffea3168b31c64af7066a6b7a5bd4d52d_u256,
    },
    // 4 words, s = 0, qh >= B
    {
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffc28939153dc8_u256,
        0x8870010238fe11cc01bfecff8619e47b7ae8508abeeea3ec8291210be85fd4cd_u256,
        0x565f018720be09e5374442f9d9d5a8f95971dd5223dba04fd292ee04a364407f_u256,
    },
    // 4 words, s = 0, q estimate 1 too large, qh >= B, subtract d
    {
        0xe3bdcc05e6add02f825f088382bcde5592caa6c54fbac550134d341a3a6338ee_u256,
        0x5b0a90ecdd3a1627832fff682ed145f47998179883020cf694b19e9f_u256,
        0x91568fb3f9cf9b425e6f5ca83906c250e3ec24e0819394ee240f60c5443bebcb_u256,
        0x24635fb45b64851594f876d162807b1ce6338bc4cb14551e8275b9779883bc29_u256,
    },
    // 4 words, subtract d from R >= B^4
    {
        0xbe1889b66bdfabdf2b3a92ac56a88bda5aefdf20162925ac778da212abf29817_u256,
        0x5ab642423f752c539b718fb17a8319fd99591b76b99adfeda8f0d90fc586a0c4_u256,
        0x370a2b6c77bd2268faf44dffcf1bfc3f10e333b98305e7c87886_u256,
        0x9106bd7caace8ac38878a047b1f9a3f093a6115b2ee35217b02_u256,
    },
};

// The paths of mulmod() with q = 0, that is d > B^(N+1) / (B + 1) for 2- to 4-word moduli: the
// estimate of q exact or 1 too large, the final subtraction of d or not.
constexpr mulmod_test_case mulmod_q0_test_cases[] = {
    // 2 words, q = 0
    {
        0xffffffffffffffffffffffffffffffffffffffffffffffffd424ae36fad18245_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ad_u256,
        0xffffffffffffffffc7dbd35c67ce2311_u256,
        0xfd83de99fdf1afb94bfc1b8b02cf3472_u256,
    },
    // 2 words, q = 0, q estimate 1 too large, subtract d
    {
        0x8000000000000000000000000000000000000000000000000000000000000_u256,
        0x8000000000000000000000000000000000000000000000_u256,
        0xffffffffffffffff0000000000000001_u256,
        0x40000000000_u256,
    },
    // 3 words, q = 0
    {
        0x4000000000000000000000000000000000000000000000000000000_u256,
        0x8000000000000000000000000000000000000_u256,
        0xffffffffffffffffdc026cd7ab077a11a467b0f92b431cd3_u256,
        0x45e9f520d9567767342c998eb259ad1040b599115a78b55_u256,
    },
    // 3 words, q = 0, q estimate 1 too large, subtract d
    {
        0x1000000000000000000000000000000000000000000000000000000000000000_u256,
        0x100000000000000000000000000000000000000000000000000000000000_u256,
        0xffffffffffffffff00000000000000010000000000000000_u256,
        0x100000000000000000000000000_u256,
    },
    // 4 words, q = 0
    {
        0xdfc6e7cdf795f2c1b33acab840ddfbc1c0ad39e2c365f21d64a8effd3ee91d03_u256,
        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3a205_u256,
        0xffffffffffffffffe8a30dc022fa63764a6bec32483543d692e9b5e1ff712717_u256,
        0xfc9ce40a79d67964b03393bf57170d4a396575be0ac30203ee2ff3b08e8b1966_u256,
    },
    // 4 words, q = 0, q estimate 1 too large, subtract d
    {
        0x1_u256,
        0xffffffffffffffffffffffffffffffffffffffffffffffffffafe62f54b2dae4_u256,
        0xffffffffffffffff0000000000000000ffffffffffffffff65a0f47d76f40e98_u256,
        0xffffffffffffffff00000000000000009a0ef1b1ddbecc4c_u256,
    },
};

TEST(uint256, mulmod_paths)
{
    for (const auto& t : mulmod_test_cases)
        EXPECT_EQ(mulmod(t.x, t.y, t.m), t.r);
    for (const auto& t : mulmod_q0_test_cases)
        EXPECT_EQ(mulmod(t.x, t.y, t.m), t.r);

    // Constant evaluation.
    static_assert(std::ranges::all_of(
        mulmod_test_cases, [](const auto& t) { return mulmod(t.x, t.y, t.m) == t.r; }));
    static_assert(std::ranges::all_of(
        mulmod_q0_test_cases, [](const auto& t) { return mulmod(t.x, t.y, t.m) == t.r; }));
}

#if INTX_HAS_BUILTIN_INT128
TEST(uint256, conversion_from_builtin_uint128)
{
    const builtin_uint128 x = (builtin_uint128{1} << 64) | builtin_uint128{2};

    const auto a = uint256{x};
    const auto b = static_cast<uint256>(x);
    const auto expected = uint256{uint64_t{2}, uint64_t{1}};

    EXPECT_EQ(a, expected);
    EXPECT_EQ(b, expected);
}
#endif
