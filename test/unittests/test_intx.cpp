// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_cases.hpp"

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace intx;

// constexpr uint64_t maximal[] = {
//    0x0000000000000000,
//    0x0000000000000001,
//    0x0000000000000002,
//    0x000000000000000f,
//    0x0000000000000010,
//    0x00000000fffffffe,
//    0x00000000ffffffff,
//    0x0000000100000000,
//    0x0000000100000001,
//    0x00000001fffffffe,
//    0x00000001ffffffff,
//    0x0000000200000000,
//    0x0000000200000001,
//    0x0fffffffffffffff,
//    0x1000000000000000,
//    0x1000000000000001,
//    0x1010101010101010,
//    0x1ffffffffffffffe,
//    0x1fffffffffffffff,
//    0x2000000000000000,
//    0x7000000000000000,
//    0x7ffffffffffffffd,
//    0x7ffffffffffffffe,
//    0x7fffffffffffffff,
//    0x8000000000000000,
//    0x8000000000000001,
//    0xfffffffffffffffd,
//    0xfffffffffffffffe,
//    0xffffffffffffffff,
//};

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
        auto& parts_set = minimal;
        for (auto a : parts_set)
        {
            for (auto b : parts_set)
            {
                for (auto c : parts_set)
                {
                    for (auto d : parts_set)
                    {
                        uint256 n;
                        n.lo = (static_cast<uint128>(a) << 64) | b;
                        n.hi = (static_cast<uint128>(c) << 64) | d;
                        numbers.emplace_back(n);
                    }
                }
            }
        }
    }
};

TEST_F(Uint256Test, count_significant_words_32)
{
    // FIXME: Test uint512.
    constexpr auto csw = count_significant_words<uint32_t, uint256>;

    uint256 x;
    EXPECT_EQ(csw(x), 0);

    x = 1;
    for (unsigned s = 0; s < 256; ++s)
        EXPECT_EQ(csw(x << s), s / 32 + 1);
}

TEST_F(Uint256Test, count_significant_words_64)
{
    // FIXME: Test uint512.
    constexpr auto csw = count_significant_words<uint64_t, uint256>;

    uint256 x;
    EXPECT_EQ(csw(x), 0);

    x = 1;
    for (unsigned s = 0; s < 256; ++s)
        EXPECT_EQ(csw(x << s), s / 64 + 1);
}

TEST_F(Uint256Test, udiv)
{
    for (auto a : numbers)
    {
        int i = 0;
        for (auto d : numbers)
        {
            if (d == 0)
                continue;

            if (a < d)
                continue;

            if (i++ > 15)  // Limit number of tests.
                break;

            auto e = udivrem(a, d);

            auto res = udiv_qr_knuth_opt_base(a, d);
            EXPECT_EQ(res.quot, e.quot)
                << to_string(a) << " / " << to_string(d) << " = " << to_string(res.quot);
            EXPECT_EQ(res.rem, e.rem)
                << to_string(a) << " % " << to_string(d) << " = " << to_string(e.rem);

            res = udiv_qr_knuth_opt(a, d);
            EXPECT_EQ(res.quot, e.quot)
                << to_string(a) << " / " << to_string(d) << " = " << to_string(res.quot);
            EXPECT_EQ(res.rem, e.rem)
                << to_string(a) << " % " << to_string(d) << " = " << to_string(res.rem);

            res = udiv_qr_knuth_hd_base(a, d);
            EXPECT_EQ(res.quot, e.quot)
                << to_string(a) << " / " << to_string(d) << " = " << to_string(res.quot);
            EXPECT_EQ(res.rem, e.rem)
                << to_string(a) << " % " << to_string(d) << " = " << to_string(res.rem);

            res = udiv_qr_knuth_llvm_base(a, d);
            EXPECT_EQ(res.quot, e.quot)
                << to_string(a) << " / " << to_string(d) << " = " << to_string(res.quot);
            EXPECT_EQ(res.rem, e.rem)
                << to_string(a) << " % " << to_string(d) << " = " << to_string(res.rem);
        }
    }
}

TEST_F(Uint256Test, add_against_sub)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            uint256 sum = add(a, b);
            uint256 test = sub(sum, b);
            EXPECT_EQ(a, test);
        }
    }
}

TEST_F(Uint256Test, simple_udiv)
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
        // if (i != 5) continue;

        const auto& data = data_set[i];
        uint256 n = from_string<uint256>(data[0]);
        uint256 d = from_string<uint256>(data[1]);
        uint256 expected_q = from_string<uint256>(data[2]);
        uint256 expected_r = from_string<uint256>(data[3]);

        auto res = udiv_qr_knuth_opt_base(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;

        res = udiv_qr_knuth_opt(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;

        res = udiv_qr_knuth_64(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;

        res = udiv_qr_knuth_hd_base(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;

        res = udiv_qr_knuth_llvm_base(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;
    }
}

TEST_F(Uint256Test, shift_one_bit)
{
    for (unsigned shift = 0; shift < 256; ++shift)
    {
        uint256 x = 1;
        uint256 y = shl(x, shift);
        uint256 z = lsr(y, shift);
        EXPECT_EQ(x, z) << "shift: " << shift;
    }
}

TEST_F(Uint256Test, shift_loop_one_bit)
{
    for (unsigned shift = 0; shift < 256; ++shift)
    {
        uint256 x = 1;
        uint256 y = shl_loop(x, shift);
        uint256 z = lsr(y, shift);
        EXPECT_EQ(x, z) << "shift: " << shift;
    }
}

TEST_F(Uint256Test, not_of_zero)
{
    uint256 ones = ~uint256(0);
    for (unsigned pos = 0; pos < 256; ++pos)
    {
        uint256 probe = shl(uint256(1), pos);
        uint256 test = probe & ones;
        EXPECT_NE(test, 0) << "bit position: " << pos;
    }
}

TEST_F(Uint256Test, shift_all_ones)
{
    for (unsigned shift = 0; shift < 256; ++shift)
    {
        uint256 x = 1;
        uint256 y = shl(x, shift);
        uint256 z = lsr(y, shift);
        EXPECT_EQ(x, z) << "shift: " << shift;
    }
}

TEST_F(Uint256Test, clz_one_bit)
{
    uint256 t = 1;
    unsigned b = num_bits(t);
    for (unsigned i = 0; i < b; ++i)
    {
        unsigned c = clz(t);
        EXPECT_EQ(c, b - 1 - i);
        t = shl(t, 1);
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
    for (auto factor : {0, 1, 2, 3, 19, 32, 577})
    {
        for (auto a : numbers)
        {
            uint256 s = 0;
            for (int i = 0; i < factor; ++i)
                s = add(s, a);

            uint256 p = mul(a, uint256(factor));
            EXPECT_EQ(p, s);
        }
    }
}

TEST(uint256, negation_overflow)
{
    auto x = -1_u256;
    auto z = 0_u256;
    EXPECT_NE(x, z);
    EXPECT_EQ(x, ~z);

    auto m = 1_u256 << 255;  // Minimal signed value.
    EXPECT_EQ(-m, m);
}

TEST(uint512, literal)
{
    auto x = 1_u512;
    static_assert(std::is_same<decltype(x), uint512>::value, "");
    EXPECT_EQ(x, 1);

    x = 0_u512;
    EXPECT_EQ(x, 0);

    x = 0xab_u512;
    EXPECT_EQ(x, 0xab);

    x = 0xab12ff00_u512;
    EXPECT_EQ(x, 0xab12ff00);
}

TEST(uint512, bswap)
{
    auto x = 1_u512;
    auto y = bswap(x);
    EXPECT_EQ(y, shl(1_u512, 504));
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
    EXPECT_EQ(exp(3_u256, 0_u256), 1);
    EXPECT_EQ(exp(3_u256, 1_u256), 3);
    EXPECT_EQ(exp(3_u256, 2_u256), 9);
    EXPECT_EQ(exp(3_u256, 20181229_u256),
        83674153047243082998136072363356897816464308069321161820168341056719375264851_u256);
}

TEST(uint256, count_significant_bytes)
{
    auto w = count_significant_words<uint8_t>(1_u256 << 113);
    EXPECT_EQ(w, 15);
    EXPECT_EQ(count_significant_words<uint8_t>(0_u256), 0);
}
