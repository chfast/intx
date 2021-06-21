// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"

using namespace intx;

TYPED_TEST(uint_test, slt)
{
    const auto max = ~TypeParam{0} >> 1;
    const auto max_m1 = max - 1;
    const auto min = TypeParam{1} << (TypeParam::num_bits - 1);
    const auto min_m1 = min + 1;
    const auto zero = TypeParam{0};
    const auto one = TypeParam{1};
    const auto neg_one = ~TypeParam{0};

    EXPECT_TRUE(slt(min, max));
    EXPECT_TRUE(slt(min, max_m1));
    EXPECT_TRUE(slt(min, one));
    EXPECT_TRUE(slt(min, zero));
    EXPECT_TRUE(slt(min, neg_one));
    EXPECT_TRUE(slt(min, min_m1));
    EXPECT_FALSE(slt(min, min));

    EXPECT_TRUE(slt(min_m1, max));
    EXPECT_TRUE(slt(min_m1, max_m1));
    EXPECT_TRUE(slt(min_m1, one));
    EXPECT_TRUE(slt(min_m1, zero));
    EXPECT_TRUE(slt(min_m1, neg_one));
    EXPECT_FALSE(slt(min_m1, min_m1));
    EXPECT_FALSE(slt(min_m1, min));

    EXPECT_TRUE(slt(neg_one, max));
    EXPECT_TRUE(slt(neg_one, max_m1));
    EXPECT_TRUE(slt(neg_one, one));
    EXPECT_TRUE(slt(neg_one, zero));
    EXPECT_FALSE(slt(neg_one, neg_one));
    EXPECT_FALSE(slt(neg_one, min_m1));
    EXPECT_FALSE(slt(neg_one, min));

    EXPECT_TRUE(slt(zero, max));
    EXPECT_TRUE(slt(zero, max_m1));
    EXPECT_TRUE(slt(zero, one));
    EXPECT_FALSE(slt(zero, zero));
    EXPECT_FALSE(slt(zero, neg_one));
    EXPECT_FALSE(slt(zero, min_m1));
    EXPECT_FALSE(slt(zero, min));

    EXPECT_TRUE(slt(one, max));
    EXPECT_TRUE(slt(one, max_m1));
    EXPECT_FALSE(slt(one, one));
    EXPECT_FALSE(slt(one, zero));
    EXPECT_FALSE(slt(one, neg_one));
    EXPECT_FALSE(slt(one, min_m1));
    EXPECT_FALSE(slt(one, min));

    EXPECT_TRUE(slt(max_m1, max));
    EXPECT_FALSE(slt(max_m1, max_m1));
    EXPECT_FALSE(slt(max_m1, one));
    EXPECT_FALSE(slt(max_m1, zero));
    EXPECT_FALSE(slt(max_m1, neg_one));
    EXPECT_FALSE(slt(max_m1, min_m1));
    EXPECT_FALSE(slt(max_m1, min));

    EXPECT_FALSE(slt(max, max));
    EXPECT_FALSE(slt(max, max_m1));
    EXPECT_FALSE(slt(max, one));
    EXPECT_FALSE(slt(max, zero));
    EXPECT_FALSE(slt(max, neg_one));
    EXPECT_FALSE(slt(max, min_m1));
    EXPECT_FALSE(slt(max, min));
}

TYPED_TEST(uint_test, bitwise)
{
    constexpr auto half_bits_count = sizeof(TypeParam) * 4;

    auto x00 = TypeParam{0b00};
    auto l01 = TypeParam{0b01};
    auto l10 = TypeParam{0b10};
    auto l11 = TypeParam{0b11};
    auto h01 = TypeParam{0b01} << half_bits_count;
    auto h10 = TypeParam{0b10} << half_bits_count;
    auto h11 = TypeParam{0b11} << half_bits_count;
    auto x11 = (TypeParam{0b11} << half_bits_count) + 0b11;

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

TYPED_TEST(uint_test, shift_one_bit)
{
    for (unsigned shift = 0; shift < sizeof(TypeParam) * 8; ++shift)
    {
        SCOPED_TRACE(shift);
        constexpr auto x = TypeParam{1};
        const auto a = x << shift;
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

TYPED_TEST(uint_test, shift_right_overflow)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = x >> n;
        EXPECT_EQ(x >> sh, 0) << "n=" << n;
    }

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = TypeParam{sizeof(TypeParam) * 8} << n;
        EXPECT_EQ(x >> sh, 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_left_overflow_uint64)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= 100; ++n)
    {
        const uint64_t sh = sizeof(TypeParam) * 8 + n;
        EXPECT_EQ(x << sh, 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_right_overflow_uint64)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= 100; ++n)
    {
        const uint64_t sh = sizeof(TypeParam) * 8 + n;
        EXPECT_EQ(x >> sh, 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_overflow)
{
    const uint64_t sh = sizeof(TypeParam) * 8;
    const auto value = ~TypeParam{};
    EXPECT_EQ(value >> sh, 0);
    EXPECT_EQ(value >> TypeParam{sh}, 0);
    EXPECT_EQ(value << sh, 0);
    EXPECT_EQ(value << TypeParam{sh}, 0);
}

TYPED_TEST(uint_test, shift_by_int)
{
    const auto x = TypeParam{1} << (sizeof(TypeParam) * 8 - 1) | TypeParam{1};
    EXPECT_EQ(x >> 0, x);
    EXPECT_EQ(x << 0, x);
    EXPECT_EQ(x >> 1, TypeParam{1} << uint64_t{TypeParam::num_bits - 2});
    EXPECT_EQ(x << 1, TypeParam{2});
    EXPECT_EQ(x >> int{TypeParam::num_bits - 1}, TypeParam{1});
    EXPECT_EQ(x << int{TypeParam::num_bits - 1}, TypeParam{1} << uint64_t{TypeParam::num_bits - 1});
    EXPECT_EQ(x >> int{TypeParam::num_bits}, 0);
    EXPECT_EQ(x << int{TypeParam::num_bits}, 0);
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
    unsigned b = TypeParam::num_bits;
    for (unsigned i = 0; i < b; ++i)
    {
        unsigned c = clz(t);
        EXPECT_EQ(c, b - 1 - i);
        t <<= 1;
    }
}

TYPED_TEST(uint_test, clz_extremes)
{
    constexpr auto num_bits = TypeParam::num_bits;
    EXPECT_EQ(clz(TypeParam{}), num_bits);
    EXPECT_EQ(clz(~TypeParam{}), 0u);
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
