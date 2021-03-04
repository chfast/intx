// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_cases.hpp"
#include "test_utils.hpp"
#include <experimental/add.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

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
                    {
                        uint256 n;
                        n.lo = uint128{a, b};
                        n.hi = uint128{c, d};
                        numbers.emplace_back(n);
                    }
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

TEST_F(Uint256Test, add_experimental)
{
    const auto n = numbers.size();
    for (size_t i = 0; i < n; ++i)
    {
        const auto a = numbers[i];
        const auto b = numbers[n - 1 - i];
        const auto s = a + b;

        EXPECT_EQ(experimental::add_recursive(a, b), s);
        EXPECT_EQ(experimental::add_waterflow(a, b), s);
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
        const auto& data = data_set[i];
        uint256 n = from_string<uint256>(data[0]);
        uint256 d = from_string<uint256>(data[1]);
        uint256 expected_q = from_string<uint256>(data[2]);
        uint256 expected_r = from_string<uint256>(data[3]);

        const auto res = udivrem(n, d);
        EXPECT_EQ(res.quot, expected_q) << "data index: " << i;
        EXPECT_EQ(res.rem, expected_r) << "data index: " << i;
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

TEST(uint256, arithmetic)
{
    for (const auto& t : arithmetic_test_cases)
    {
        EXPECT_EQ(t.x + t.y, t.sum);
        EXPECT_EQ(t.y + t.x, t.sum);
        EXPECT_EQ(experimental::add_recursive(t.x, t.y), t.sum);
        EXPECT_EQ(experimental::add_waterflow(t.x, t.y), t.sum);
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

TEST(uint256, count_significant_bytes)
{
    auto w = count_significant_words<uint8_t>(1_u256 << 113);
    EXPECT_EQ(w, 15u);
    EXPECT_EQ(count_significant_words<uint8_t>(0_u256), 0u);
}

TEST(uint256, addmod)
{
    const auto x = 0xab0f4afc4c78548d4c30e1ab3449e3_u128;
    const auto y = 0xf0a4485af15508e448cdddb0d1301664_u128;
    const auto mod = 0xf0f9d0006f7b450e8f73f621a6ca3b56_u128;
    EXPECT_EQ(addmod(x, y, mod), 0x5587a57e263c2a46a61870d59a24f1_u128);
    const auto a = 0xdce049946eccbbf77ed1e8e2a3c89e15a8e897df2194150700f5096dea864cdb_u256;
    const auto b = 0x397dd0df188eaffbf5216c6be56fe49002fbdc23b95a58a60f69e56f6f87f424_u256;
    EXPECT_EQ(addmod(a, b, mod), 0x7533da49e8c499530049fbf08733976b_u128);
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


template <typename T>
class uint_test : public testing::Test
{
};

using types = testing::Types<uint128, uint256, uint512>;
TYPED_TEST_SUITE(uint_test, types, type_to_name);

TYPED_TEST(uint_test, numeric_limits)
{
    static_assert(std::numeric_limits<uint256>::digits10 == 77, "");
    static_assert(std::numeric_limits<uint512>::digits10 == 154, "");

    static_assert(!std::numeric_limits<TypeParam>::is_signed, "");
    static_assert(std::numeric_limits<TypeParam>::is_integer, "");
    static_assert(std::numeric_limits<TypeParam>::is_exact, "");
    static_assert(std::numeric_limits<TypeParam>::radix == 2, "");

    static_assert(std::numeric_limits<TypeParam>::min() == 0, "");
    static_assert(std::numeric_limits<TypeParam>::max() == TypeParam{0} - 1, "");

    EXPECT_EQ(std::numeric_limits<TypeParam>::min(), 0);
    EXPECT_EQ(std::numeric_limits<TypeParam>::max(), TypeParam{0} - 1);
}

TYPED_TEST(uint_test, comparison)
{
    auto z00 = TypeParam{0, 0};
    auto z01 = TypeParam{0, 1};
    auto z10 = TypeParam{1, 0};
    auto z11 = TypeParam{1, 1};

    EXPECT_EQ(z00, z00);
    EXPECT_EQ(z01, z01);
    EXPECT_EQ(z10, z10);
    EXPECT_EQ(z11, z11);

    EXPECT_NE(z00, z01);
    EXPECT_NE(z00, z10);
    EXPECT_NE(z00, z11);
    EXPECT_NE(z10, z00);
    EXPECT_NE(z10, z01);
    EXPECT_NE(z10, z11);

    EXPECT_LT(z00, z01);
    EXPECT_LT(z00, z10);
    EXPECT_LT(z00, z11);
    EXPECT_LT(z01, z10);
    EXPECT_LT(z01, z11);
    EXPECT_LT(z10, z11);

    EXPECT_LE(z00, z00);
    EXPECT_LE(z00, z01);
    EXPECT_LE(z00, z10);
    EXPECT_LE(z00, z11);
    EXPECT_LE(z01, z01);
    EXPECT_LE(z01, z10);
    EXPECT_LE(z01, z11);
    EXPECT_LE(z10, z10);
    EXPECT_LE(z10, z11);
    EXPECT_LE(z11, z11);

    EXPECT_GT(z01, z00);
    EXPECT_GT(z10, z00);
    EXPECT_GT(z11, z00);
    EXPECT_GT(z10, z01);
    EXPECT_GT(z11, z01);
    EXPECT_GT(z11, z10);

    EXPECT_GE(z00, z00);
    EXPECT_GE(z01, z00);
    EXPECT_GE(z10, z00);
    EXPECT_GE(z11, z00);
    EXPECT_GE(z01, z01);
    EXPECT_GE(z10, z01);
    EXPECT_GE(z11, z01);
    EXPECT_GE(z10, z10);
    EXPECT_GE(z11, z10);
    EXPECT_GE(z11, z11);
}

TYPED_TEST(uint_test, bitwise)
{
    auto x00 = TypeParam{0b00};
    auto l01 = TypeParam{0b01};
    auto l10 = TypeParam{0b10};
    auto l11 = TypeParam{0b11};
    auto h01 = TypeParam{0b01, 0};
    auto h10 = TypeParam{0b10, 0};
    auto h11 = TypeParam{0b11, 0};
    auto x11 = TypeParam{0b11, 0b11};

    EXPECT_EQ(x00 | l01 | l10 | l11, l11);
    EXPECT_EQ(x00 | h01 | h10 | h11, h11);
    EXPECT_EQ(l10 | l01 | h10 | h01, x11);

    EXPECT_EQ(l01 & l10 & l11, 0);
    EXPECT_EQ(h01 & h10 & h11, 0);
    EXPECT_EQ(l01 & l11, l01);
    EXPECT_EQ(h01 & h11, h01);
    EXPECT_EQ(h11 & l11, 0);

    EXPECT_EQ(l01 ^ l10, l11);
    EXPECT_EQ(l11 ^ l10, l01);
    EXPECT_EQ(h01 ^ h10, h11);
    EXPECT_EQ(h11 ^ h10, h01);
}

TYPED_TEST(uint_test, negation_overflow)
{
    auto x = -TypeParam{1};
    auto z = TypeParam{0};
    EXPECT_NE(x, z);
    EXPECT_EQ(x, ~z);

    auto m = TypeParam{1} << (sizeof(TypeParam) * 8 - 1);  // Minimal signed value.
    EXPECT_EQ(-m, m);
}

TYPED_TEST(uint_test, shift_one_bit)
{
    for (unsigned shift = 0; shift < sizeof(TypeParam) * 8; ++shift)
    {
        SCOPED_TRACE(shift);
        constexpr auto x = TypeParam{1};

        const auto a = x << shift;
        const auto b = shl_loop(x, shift);
        EXPECT_EQ(b, a);

        EXPECT_EQ(x, a >> shift);
    }
}

TYPED_TEST(uint_test, shift_left_overflow)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = x >> n;
        EXPECT_EQ(x << sh, 0) << "n=" << n;
    }

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = TypeParam{sizeof(TypeParam) * 8} << n;
        EXPECT_EQ(x << sh, 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_overflow)
{
    unsigned sh = sizeof(TypeParam) * 8;
    const auto value = ~TypeParam{};
    EXPECT_EQ(value >> sh, 0);
    EXPECT_EQ(value >> TypeParam{sh}, 0);
    EXPECT_EQ(value << sh, 0);
    EXPECT_EQ(value << TypeParam{sh}, 0);
    EXPECT_EQ(shl_loop(value, sh), 0);
}

TYPED_TEST(uint_test, not_of_zero)
{
    auto ones = ~TypeParam{};
    for (unsigned pos = 0; pos < sizeof(TypeParam) * 8; ++pos)
        EXPECT_NE((TypeParam{1} << pos) & ones, 0);
}

TYPED_TEST(uint_test, clz_one_bit)
{
    auto t = TypeParam{1};
    unsigned b = num_bits(t);
    for (unsigned i = 0; i < b; ++i)
    {
        unsigned c = clz(t);
        EXPECT_EQ(c, b - 1 - i);
        t <<= 1;
    }
}

TYPED_TEST(uint_test, shift_against_mul)
{
    auto a = TypeParam{0xaaaaaaa};
    auto b = TypeParam{200};

    auto x = a << b;
    auto s = TypeParam{1} << b;
    auto y = a * s;
    EXPECT_EQ(x, y);
}

TYPED_TEST(uint_test, count_significant_words_32)
{
    constexpr auto csw = count_significant_words<uint32_t, TypeParam>;

    TypeParam x;
    EXPECT_EQ(csw(x), 0u);

    x = 1;
    for (size_t s = 0; s < sizeof(TypeParam) * 8; ++s)
        EXPECT_EQ(csw(x << s), s / 32 + 1);
}

TYPED_TEST(uint_test, count_significant_words_64)
{
    constexpr auto csw = count_significant_words<uint64_t, TypeParam>;

    TypeParam x;
    EXPECT_EQ(csw(x), 0u);

    x = 1;
    for (size_t s = 0; s < sizeof(TypeParam) * 8; ++s)
        EXPECT_EQ(csw(x << s), s / 64 + 1);
}

TYPED_TEST(uint_test, bswap)
{
    auto x = TypeParam{1};
    EXPECT_EQ(bswap(x), x << ((sizeof(x) - 1) * 8));
}

TYPED_TEST(uint_test, endianness)
{
    constexpr auto s = sizeof(TypeParam);

    uint8_t data[s];
    const auto x = TypeParam{1};

    le::store(data, x);
    EXPECT_EQ(data[0], 1);
    EXPECT_EQ(data[s - 1], 0);
    EXPECT_EQ(le::load<TypeParam>(data), x);

    be::store(data, x);
    EXPECT_EQ(data[0], 0);
    EXPECT_EQ(data[s - 1], 1);
    EXPECT_EQ(be::load<TypeParam>(data), x);

    be::unsafe::store(data, x);
    EXPECT_EQ(data[0], 0);
    EXPECT_EQ(data[s - 1], 1);
    EXPECT_EQ(be::unsafe::load<TypeParam>(data), x);
}

TYPED_TEST(uint_test, be_zext)
{
    uint8_t data[] = {0x01, 0x02, 0x03};
    const auto x = be::load<TypeParam>(data);
    EXPECT_EQ(x, 0x010203);
}

TYPED_TEST(uint_test, be_load)
{
    constexpr auto size = sizeof(TypeParam);
    uint8_t data[size]{};
    data[0] = 0x80;
    data[size - 1] = 1;
    const auto x = be::load<TypeParam>(data);
    EXPECT_EQ(x, (TypeParam{1} << (TypeParam::num_bits - 1)) | 1);
}

TYPED_TEST(uint_test, be_store)
{
    const auto x = TypeParam{0x0201};
    uint8_t data[sizeof(x)];
    be::store(data, x);
    EXPECT_EQ(data[sizeof(x) - 1], 1);
    EXPECT_EQ(data[sizeof(x) - 2], 2);
    EXPECT_EQ(data[sizeof(x) - 3], 0);
    EXPECT_EQ(data[0], 0);
}

TYPED_TEST(uint_test, be_trunc)
{
    constexpr auto x = TypeParam{0xee48656c6c6f20536f6c617269732121_u128};
    uint8_t out[15];
    be::trunc(out, x);
    const auto str = std::string{reinterpret_cast<char*>(out), sizeof(out)};
    EXPECT_EQ(str, "Hello Solaris!!");
}

template <size_t M>
struct storage
{
    uint8_t bytes[M];
};

TYPED_TEST(uint_test, typed_store)
{
    const auto x = TypeParam{2};
    const auto s = be::store<storage<sizeof(x)>>(x);
    EXPECT_EQ(s.bytes[sizeof(x) - 1], 2);
}

TYPED_TEST(uint_test, typed_trunc)
{
    const auto x = TypeParam{0xaabb};
    const auto s = be::trunc<storage<9>>(x);
    EXPECT_EQ(s.bytes[8], 0xbb);
    EXPECT_EQ(s.bytes[7], 0xaa);
    EXPECT_EQ(s.bytes[6], 0);
    EXPECT_EQ(s.bytes[0], 0);
}

TYPED_TEST(uint_test, typed_load_zext)
{
    const auto s = storage<1>({0xed});
    const auto x = be::load<TypeParam>(s);
    EXPECT_EQ(x, 0xed);
}

TYPED_TEST(uint_test, typed_load)
{
    const auto s = storage<sizeof(TypeParam)>({0x88});
    const auto x = be::load<TypeParam>(s);
    EXPECT_EQ(x, TypeParam{0x88} << (TypeParam::num_bits - 8));
}


TYPED_TEST(uint_test, convert_to_bool)
{
    EXPECT_TRUE((TypeParam{1, 0}));
    EXPECT_TRUE((TypeParam{0, 1}));
    EXPECT_TRUE((TypeParam{1, 1}));
    EXPECT_TRUE((TypeParam{2, 0}));
    EXPECT_TRUE((TypeParam{0, 2}));
    EXPECT_TRUE((TypeParam{2, 2}));
    EXPECT_FALSE((TypeParam{0, 0}));
}

TYPED_TEST(uint_test, string_conversions)
{
    auto values = {
        TypeParam{1} << (sizeof(TypeParam) * 8 - 1),
        TypeParam{0},
        TypeParam{1, 0},
        TypeParam{1, 1},
        ~TypeParam{1},
        ~TypeParam{0},
    };

    for (auto v : values)
    {
        auto s = to_string(v);
        auto x = from_string<TypeParam>(s);
        EXPECT_EQ(x, v);
    }
}

TYPED_TEST(uint_test, to_string_base)
{
    auto x = TypeParam{1024};
    EXPECT_THROW_MESSAGE(to_string(x, 1), std::invalid_argument, "invalid base");
    EXPECT_THROW_MESSAGE(to_string(x, 37), std::invalid_argument, "invalid base");
    EXPECT_EQ(to_string(x, 10), "1024");
    EXPECT_EQ(to_string(x, 16), "400");
    EXPECT_EQ(to_string(x, 36), "sg");
    EXPECT_EQ(to_string(x, 2), "10000000000");
    EXPECT_EQ(to_string(x, 8), "2000");
}

TYPED_TEST(uint_test, as_bytes)
{
    constexpr auto x = TypeParam{0xa05};
    const auto b = as_bytes(x);
    EXPECT_EQ(b[0], 5);
    EXPECT_EQ(b[1], 0xa);

    auto y = x;
    auto d = as_bytes(y);
    d[0] = 3;
    d[1] = 0xc;
    EXPECT_EQ(y, 0xc03);
}
