// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test/experimental/shift.hpp"
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

TYPED_TEST(uint_test, shift_one_bit_exp)
{
    for (unsigned shift = 0; shift < sizeof(TypeParam) * 8; ++shift)
    {
        SCOPED_TRACE(shift);
        constexpr auto x = TypeParam{1};
        const auto a = experimental::shl_c(x, shift);
        EXPECT_EQ(x, experimental::shr_c(a, shift));

        const auto b = experimental::shl_e(x, shift);
        const auto c = experimental::shl_w(x, shift);
        EXPECT_EQ(b, c);
        EXPECT_EQ(x, experimental::shr_c(b, shift));
    }
}

TYPED_TEST(uint_test, shift_left_overflow_exp)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = experimental::shr_c(x, n);
        EXPECT_EQ(experimental::shl_c(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_e(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_e(x, sh), 0) << "n=" << n;
    }

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = experimental::shl_c(TypeParam{sizeof(TypeParam) * 8}, n);
        const auto sh2 = experimental::shl_e(TypeParam{sizeof(TypeParam) * 8}, n);
        const auto sh3 = experimental::shl_e(TypeParam{sizeof(TypeParam) * 8}, n);
        EXPECT_EQ(sh, sh2);
        EXPECT_EQ(sh, sh3);
        EXPECT_EQ(experimental::shl_c(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_e(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_w(x, sh), 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_right_overflow_exp)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = experimental::shr_c(x, n);
        EXPECT_EQ(experimental::shr_c(x, sh), 0) << "n=" << n;
    }

    for (unsigned n = 0; n <= sizeof(TypeParam) * 7; ++n)
    {
        const auto sh = experimental::shl_c(TypeParam{sizeof(TypeParam) * 8}, n);
        const auto sh2 = experimental::shl_e(TypeParam{sizeof(TypeParam) * 8}, n);
        const auto sh3 = experimental::shl_w(TypeParam{sizeof(TypeParam) * 8}, n);
        EXPECT_EQ(sh, sh2);
        EXPECT_EQ(sh, sh3);
        EXPECT_EQ(experimental::shr_c(x, sh), 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_left_overflow_uint64_exp)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= 100; ++n)
    {
        const uint64_t sh = sizeof(TypeParam) * 8 + n;
        EXPECT_EQ(experimental::shl_c(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_e(x, sh), 0) << "n=" << n;
        EXPECT_EQ(experimental::shl_w(x, sh), 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_right_overflow_uint64_exp)
{
    const auto x = ~TypeParam{};

    for (unsigned n = 0; n <= 100; ++n)
    {
        const uint64_t sh = sizeof(TypeParam) * 8 + n;
        EXPECT_EQ(experimental::shr_c(x, sh), 0) << "n=" << n;
    }
}

TYPED_TEST(uint_test, shift_overflow_exp)
{
    const uint64_t sh = sizeof(TypeParam) * 8;
    const auto value = ~TypeParam{};
    EXPECT_EQ(experimental::shr_c(value, sh), 0);
    EXPECT_EQ(experimental::shr_c(value, TypeParam{sh}), 0);
    EXPECT_EQ(experimental::shl_c(value, sh), 0);
    EXPECT_EQ(experimental::shl_c(value, TypeParam{sh}), 0);
}

TYPED_TEST(uint_test, shift_by_int_exp)
{
    const auto x = experimental::shl_c(TypeParam{1}, (sizeof(TypeParam) * 8 - 1)) | TypeParam{1};
    EXPECT_EQ(experimental::shr_c(x, 0), x);
    EXPECT_EQ(experimental::shl_c(x, 0), x);
    EXPECT_EQ(experimental::shl_e(x, 0), x);
    EXPECT_EQ(experimental::shl_w(x, 0), x);
    EXPECT_EQ(experimental::shr_c(x, 1),
        experimental::shl_c(TypeParam{1}, uint64_t{TypeParam::num_bits - 2}));
    EXPECT_EQ(experimental::shl_c(x, 1), TypeParam{2});
    EXPECT_EQ(experimental::shl_e(x, 1), TypeParam{2});
    EXPECT_EQ(experimental::shl_w(x, 1), TypeParam{2});
    EXPECT_EQ(experimental::shr_c(x, int{TypeParam::num_bits - 1}), TypeParam{1});
    EXPECT_EQ(experimental::shl_c(x, int{TypeParam::num_bits - 1}),
        experimental::shl_c(TypeParam{1}, uint64_t{TypeParam::num_bits - 1}));
    EXPECT_EQ(experimental::shl_e(x, int{TypeParam::num_bits - 1}),
        experimental::shl_e(TypeParam{1}, uint64_t{TypeParam::num_bits - 1}));
    EXPECT_EQ(experimental::shl_w(x, int{TypeParam::num_bits - 1}),
        experimental::shl_w(TypeParam{1}, uint64_t{TypeParam::num_bits - 1}));
    EXPECT_EQ(experimental::shr_c(x, int{TypeParam::num_bits}), 0);
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

TEST(avx, shl_words)
{
    const auto x = 0x18191a1b1c1d1e1f28292a2b2c2d2e2f38393a3b3c3d3e3f48494a4b4c4d4e4f_u256;
    EXPECT_EQ(experimental::shl_words_avx(x, 0), x);
    EXPECT_EQ(experimental::shl_words_avx(x, 1), x << 64);
    EXPECT_EQ(experimental::shl_words_avx(x, 2), x << 128);
    EXPECT_EQ(experimental::shl_words_avx(x, 3), x << 192);
    EXPECT_EQ(experimental::shl_words_avx(x, 4), 0);
    EXPECT_EQ(experimental::shl_words_avx(x, 5), 0);
    EXPECT_EQ(experimental::shl_words_avx(x, 123131231), 0);
}

TEST(avx, shl_bits)
{
    const auto x = 0x18191a1b1c1d1e1f28292a2b2c2d2e2f38393a3b3c3d3e3f48494a4b4c4d4e4f_u256;
    EXPECT_EQ(experimental::shl_bits_avx(x, 0), x);
    EXPECT_EQ(experimental::shl_bits_avx(x, 1), x << 1);
    EXPECT_EQ(experimental::shl_bits_avx(x, 2), x << 2);
    EXPECT_EQ(experimental::shl_bits_avx(x, 3), x << 3);
    EXPECT_EQ(experimental::shl_bits_avx(x, 31), x << 31);
    EXPECT_EQ(experimental::shl_bits_avx(x, 32), x << 32);
    EXPECT_EQ(experimental::shl_bits_avx(x, 33), x << 33);
    EXPECT_EQ(experimental::shl_bits_avx(x, 63), x << 63);
    EXPECT_EQ(experimental::shl_bits_avx(x, 64), x << 64);
}

TEST(avx, shl_avx)
{
    const auto x = 0x18191a1b1c1d1e1f28292a2b2c2d2e2f38393a3b3c3d3e3f48494a4b4c4d4e4f_u256;
    EXPECT_EQ(experimental::shl_avx(x, 0), x);
    EXPECT_EQ(experimental::shl_avx(x, 1), x << 1);
    EXPECT_EQ(experimental::shl_avx(x, 2), x << 2);
    EXPECT_EQ(experimental::shl_avx(x, 3), x << 3);
    EXPECT_EQ(experimental::shl_avx(x, 31), x << 31);
    EXPECT_EQ(experimental::shl_avx(x, 32), x << 32);
    EXPECT_EQ(experimental::shl_avx(x, 33), x << 33);
    EXPECT_EQ(experimental::shl_avx(x, 63), x << 63);
    EXPECT_EQ(experimental::shl_avx(x, 64), x << 64);
    EXPECT_EQ(experimental::shl_avx(x, 65), x << 65);
    EXPECT_EQ(experimental::shl_avx(x, 255), x << 255);
}
