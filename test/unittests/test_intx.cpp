// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"

using namespace intx;

TYPED_TEST(uint_test, numeric_limits)
{
    static_assert(std::numeric_limits<uint256>::digits10 == 77);
    static_assert(std::numeric_limits<uint512>::digits10 == 154);

    static_assert(!std::numeric_limits<TypeParam>::is_signed);
    static_assert(std::numeric_limits<TypeParam>::is_integer);
    static_assert(std::numeric_limits<TypeParam>::is_exact);
    static_assert(std::numeric_limits<TypeParam>::radix == 2);

    static_assert(std::numeric_limits<TypeParam>::min() == 0);
    static_assert(std::numeric_limits<TypeParam>::max() == TypeParam{0} - 1);

    EXPECT_EQ(std::numeric_limits<TypeParam>::min(), 0);
    EXPECT_EQ(std::numeric_limits<TypeParam>::max(), TypeParam{0} - 1);
}

TYPED_TEST(uint_test, comparison)
{
    constexpr auto half_words_count = TypeParam::num_words / 2;

    auto z00 = TypeParam{0};
    auto z01 = TypeParam{1};
    auto z10 = TypeParam{0};
    z10[half_words_count] = 1;
    auto z11 = TypeParam{1};
    z11[half_words_count] = 1;

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

TYPED_TEST(uint_test, negation_overflow)
{
    auto x = -TypeParam{1};
    auto z = TypeParam{0};
    EXPECT_NE(x, z);
    EXPECT_EQ(x, ~z);

    auto m = TypeParam{1} << (sizeof(TypeParam) * 8 - 1);  // Minimal signed value.
    EXPECT_EQ(-m, m);
}

TYPED_TEST(uint_test, count_significant_words_64)
{
    TypeParam x;
    EXPECT_EQ(count_significant_words(x), 0u);

    x = 1;
    for (size_t s = 0; s < sizeof(TypeParam) * 8; ++s)
        EXPECT_EQ(count_significant_words(x << s), s / 64 + 1);
}

TYPED_TEST(uint_test, count_significant_bytes)
{
    static_assert(count_significant_bytes(TypeParam{0}) == 0);
    static_assert(count_significant_bytes(TypeParam{1}) == 1);
    static_assert(count_significant_bytes(TypeParam{0x80}) == 1);
    static_assert(count_significant_bytes(TypeParam{0x100000000000000}) == 8);
    static_assert(
        count_significant_bytes(TypeParam{1} << (TypeParam::num_bits - 8)) == sizeof(TypeParam));
    static_assert(
        count_significant_bytes(TypeParam{1} << (TypeParam::num_bits - 1)) == sizeof(TypeParam));

    TypeParam x;
    EXPECT_EQ(count_significant_bytes(x), 0u);
    x = 1;
    EXPECT_EQ(count_significant_bytes(x), 1u);
    x <<= TypeParam::num_bits - 1;
    EXPECT_EQ(count_significant_bytes(x), sizeof(TypeParam));
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
    constexpr auto half_bits_count = sizeof(TypeParam) * 4;
    EXPECT_TRUE((TypeParam{1}));
    EXPECT_TRUE((TypeParam{1} << half_bits_count));
    EXPECT_TRUE((TypeParam{1} << half_bits_count) + 1);
    EXPECT_TRUE((TypeParam{2}));
    EXPECT_TRUE((TypeParam{2} << half_bits_count));
    EXPECT_TRUE((TypeParam{2} << half_bits_count) + 2);
    EXPECT_FALSE((TypeParam{0}));
}

TYPED_TEST(uint_test, string_conversions)
{
    auto values = {
        TypeParam{1} << (sizeof(TypeParam) * 8 - 1),
        TypeParam{0},
        TypeParam{1} << (sizeof(TypeParam) * 4 - 1),
        (TypeParam{1} << (sizeof(TypeParam) * 4 - 1)) | 1,
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
    constexpr auto x = to_little_endian(TypeParam{0xa05});
    const auto b = as_bytes(x);
    EXPECT_EQ(b[0], 5);
    EXPECT_EQ(b[1], 0xa);

    auto y = x;
    auto d = as_bytes(y);
    d[0] = 3;
    d[1] = 0xc;
    y = to_little_endian(y);
    EXPECT_EQ(y, 0xc03);
}
