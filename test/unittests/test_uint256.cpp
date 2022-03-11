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

TEST(uint512, literal)
{
    auto x = 1_u512;
    static_assert(std::is_same<decltype(x), uint512>::value);
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
}

static decltype(&addmod) addmod_impls[] = {
    addmod,
    test::addmod_public,
    test::addmod_simple,
    test::addmod_prenormalize,
    test::addmod_daosvik_v1,
    test::addmod_daosvik_v2,
};

TEST(uint256, addmod)
{
    for (auto&& impl : addmod_impls)
    {
        const auto x = 0xab0f4afc4c78548d4c30e1ab3449e3_u128;
        const auto y = 0xf0a4485af15508e448cdddb0d1301664_u128;
        const auto mod = 0xf0f9d0006f7b450e8f73f621a6ca3b56_u128;
        EXPECT_EQ(impl(x, y, mod), 0x5587a57e263c2a46a61870d59a24f1_u128);
        const auto a = 0xdce049946eccbbf77ed1e8e2a3c89e15a8e897df2194150700f5096dea864cdb_u256;
        const auto b = 0x397dd0df188eaffbf5216c6be56fe49002fbdc23b95a58a60f69e56f6f87f424_u256;
        EXPECT_EQ(impl(a, b, mod), 0x7533da49e8c499530049fbf08733976b_u128);
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
    const auto x = 0xab0f4afc4c78548d4c30e1ab3449e3_u128;
    const auto y = 0xf0a4485af15508e448cdddb0d1301664_u128;
    const auto mod = 0xf0f9d0006f7b450e8f73f621a6ca3b56_u128;
    EXPECT_EQ(mulmod(x, y, mod), 0x6c5c6c6fb72967583930f380c2a5269c_u128);
    const auto a = 0x4028c97ce32bf74a3a3137956b07a5a699ca8422bdf672f547_u256;
    const auto b = 0x8c9f09b6227ba6542a97343c679e1d11d8bfa29228c18615c2_u256;
    EXPECT_EQ(mulmod(a, b, mod), 0xca283039a2ad0dbd3d60fbadb29e9c7a_u128);
}
