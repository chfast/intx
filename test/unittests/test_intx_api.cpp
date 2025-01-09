// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"

using namespace intx::literals;

static_assert(1_u128);
static_assert(1_u192);
static_assert(1_u256);
static_assert(1_u320);
static_assert(1_u384);
static_assert(1_u448);
static_assert(1_u512);

using namespace intx;

static_assert(uint128{2} + uint128{2} == 4);
static_assert(uint256{2} + uint256{2} == 4);
static_assert(uint512{2} + uint512{2} == 4);

static_assert(uint128{2} - uint128{1} == 1);
static_assert(uint256{2} - uint256{1} == 1);
static_assert(uint512{2} - uint512{1} == 1);

static_assert(uint128{2} * uint128{2} == 4);
static_assert(uint256{2} * uint256{2} == 4);
static_assert(uint512{2} * uint512{2} == 4);

static_assert(umul(uint256{2}, uint256{3}) == 6);

static_assert(0_u256 == 0);
static_assert(-1_u256 == ~0_u256);
static_assert(
    115792089237316195423570985008687907853269984665640564039457584007913129639935_u256 == ~0_u256);
static_assert(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u256 == ~0_u256);

static_assert(clz(uint128{0}) == 128);
static_assert(clz(uint128{1}) == 127);
static_assert(clz(uint256{0}) == 256);
static_assert(clz(uint256{1}) == 255);
static_assert(clz(uint512{0}) == 512);
static_assert(clz(uint512{1}) == 511);

TEST(uint256, div)
{
    uint256 a = 10001;
    uint256 b = 10;

    EXPECT_EQ(a / b, 1000);
}


template <typename T>
class uint_api : public testing::Test
{
};

TYPED_TEST_SUITE(uint_api, test_types, type_to_name);

TYPED_TEST(uint_api, constructor)
{
    int i = -1;
    auto x = TypeParam{i};
    TypeParam y = i;
    auto z = TypeParam(i);

    EXPECT_EQ(x, y);
    EXPECT_EQ(x, z);
}

TYPED_TEST(uint_api, arithmetic)
{
    int a = 0;
    uint64_t b = 0;
    uint128 c = 0;
    uint256 d = 0;

    TypeParam x;

    EXPECT_TRUE(x + x == 0);
    EXPECT_TRUE(x + a == 0);
    EXPECT_TRUE(x + b == 0);
    EXPECT_TRUE(x + c == 0);
    EXPECT_TRUE(x + d == 0);

    EXPECT_TRUE(a + x == 0);
    EXPECT_TRUE(b + x == 0);
    EXPECT_TRUE(c + x == 0);
    EXPECT_TRUE(d + x == 0);

    EXPECT_TRUE(x - x == 0);
    EXPECT_TRUE(x - a == 0);
    EXPECT_TRUE(x - b == 0);
    EXPECT_TRUE(x - c == 0);
    EXPECT_TRUE(x - d == 0);

    EXPECT_TRUE(a - x == 0);
    EXPECT_TRUE(b - x == 0);
    EXPECT_TRUE(c - x == 0);
    EXPECT_TRUE(d - x == 0);

    EXPECT_TRUE(x * x == 0);
    EXPECT_TRUE(x * a == 0);
    EXPECT_TRUE(x * b == 0);
    EXPECT_TRUE(x * c == 0);
    EXPECT_TRUE(x * d == 0);

    EXPECT_TRUE(a * x == 0);
    EXPECT_TRUE(b * x == 0);
    EXPECT_TRUE(c * x == 0);
    EXPECT_TRUE(d * x == 0);
}


TYPED_TEST(uint_api, division)
{
    int a = 1;
    uint64_t b = 1;
    uint128 c = 1;
    uint256 d = 1;

    auto x = TypeParam{1};

    EXPECT_TRUE(x / x == 1);
    EXPECT_TRUE(x / a == 1);
    EXPECT_TRUE(x / b == 1);
    EXPECT_TRUE(x / c == 1);
    EXPECT_TRUE(x / d == 1);

    EXPECT_TRUE(a / x == 1);
    EXPECT_TRUE(b / x == 1);
    EXPECT_TRUE(c / x == 1);
    EXPECT_TRUE(d / x == 1);

    EXPECT_TRUE(x % x == 0);
    EXPECT_TRUE(x % a == 0);
    EXPECT_TRUE(x % b == 0);
    EXPECT_TRUE(x % c == 0);
    EXPECT_TRUE(x % d == 0);

    EXPECT_TRUE(a % x == 0);
    EXPECT_TRUE(b % x == 0);
    EXPECT_TRUE(c % x == 0);
    EXPECT_TRUE(d % x == 0);
}


TYPED_TEST(uint_api, bitwise)
{
    int a = 0;
    uint64_t b = 0;
    uint128 c = 0;
    uint256 d = 0;

    TypeParam x;

    EXPECT_TRUE((x | x) == 0);
    EXPECT_TRUE((x | a) == 0);
    EXPECT_TRUE((x | b) == 0);
    EXPECT_TRUE((x | c) == 0);
    EXPECT_TRUE((x | d) == 0);

    EXPECT_TRUE((a | x) == 0);
    EXPECT_TRUE((b | x) == 0);
    EXPECT_TRUE((c | x) == 0);
    EXPECT_TRUE((d | x) == 0);

    EXPECT_TRUE((x & x) == 0);
    EXPECT_TRUE((x & a) == 0);
    EXPECT_TRUE((x & b) == 0);
    EXPECT_TRUE((x & c) == 0);
    EXPECT_TRUE((x & d) == 0);

    EXPECT_TRUE((a & x) == 0);
    EXPECT_TRUE((b & x) == 0);
    EXPECT_TRUE((c & x) == 0);
    EXPECT_TRUE((d & x) == 0);

    EXPECT_TRUE((x ^ x) == 0);
    EXPECT_TRUE((x ^ a) == 0);
    EXPECT_TRUE((x ^ b) == 0);
    EXPECT_TRUE((x ^ c) == 0);
    EXPECT_TRUE((x ^ d) == 0);

    EXPECT_TRUE((a ^ x) == 0);
    EXPECT_TRUE((b ^ x) == 0);
    EXPECT_TRUE((c ^ x) == 0);
    EXPECT_TRUE((d ^ x) == 0);
}

TYPED_TEST(uint_api, comparison)
{
    int a = 3;
    uint64_t b = 5;
    uint128 c = 7;
    uint256 d = 11;

    TypeParam x;

    EXPECT_FALSE(x == a);
    EXPECT_FALSE(a == x);
    EXPECT_FALSE(x == b);
    EXPECT_FALSE(b == x);
    EXPECT_FALSE(x == c);
    EXPECT_FALSE(c == x);
    EXPECT_FALSE(x == d);
    EXPECT_FALSE(d == x);

    EXPECT_FALSE(x != x);
    EXPECT_TRUE(x != a);
    EXPECT_TRUE(a != x);
    EXPECT_TRUE(x != b);
    EXPECT_TRUE(b != x);
    EXPECT_TRUE(x != c);
    EXPECT_TRUE(c != x);
    EXPECT_TRUE(x != d);
    EXPECT_TRUE(d != x);

    EXPECT_FALSE(x < x);
    EXPECT_TRUE(x < a);
    EXPECT_TRUE(x < b);
    EXPECT_TRUE(x < c);
    EXPECT_TRUE(x < d);
    EXPECT_FALSE(a < x);
    EXPECT_FALSE(b < x);
    EXPECT_FALSE(c < x);
    EXPECT_FALSE(d < x);

    EXPECT_FALSE(x > x);
    EXPECT_FALSE(x > a);
    EXPECT_FALSE(x > b);
    EXPECT_FALSE(x > c);
    EXPECT_FALSE(x > d);
    EXPECT_TRUE(a > x);
    EXPECT_TRUE(b > x);
    EXPECT_TRUE(c > x);
    EXPECT_TRUE(d > x);

    EXPECT_TRUE(x <= x);
    EXPECT_TRUE(x <= a);
    EXPECT_TRUE(x <= b);
    EXPECT_TRUE(x <= c);
    EXPECT_TRUE(x <= d);
    EXPECT_FALSE(a <= x);
    EXPECT_FALSE(b <= x);
    EXPECT_FALSE(c <= x);
    EXPECT_FALSE(d <= x);

    EXPECT_TRUE(x >= x);
    EXPECT_FALSE(x >= a);
    EXPECT_FALSE(x >= b);
    EXPECT_FALSE(x >= c);
    EXPECT_FALSE(x >= d);
    EXPECT_TRUE(a >= x);
    EXPECT_TRUE(b >= x);
    EXPECT_TRUE(c >= x);
    EXPECT_TRUE(d >= x);
}

TYPED_TEST(uint_api, spaceship_operator)
{
    auto a = uint256{1};
    auto b = uint256{2};
    auto c = uint256{3};

    EXPECT_EQ(a <=> a, 0);
    EXPECT_EQ(a <=> b, -1);
    EXPECT_EQ(a <=> c, -1);
    EXPECT_EQ(b <=> a, 1);
    EXPECT_EQ(b <=> b, 0);
    EXPECT_EQ(b <=> c, -1);
    EXPECT_EQ(c <=> a, 1);
    EXPECT_EQ(c <=> b, 1);
    EXPECT_EQ(c <=> c, 0);

    auto d = uint128{1};
    auto e = uint128{2};
    auto f = uint128{3};

    EXPECT_EQ(d <=> d, 0);
    EXPECT_EQ(d <=> e, -1);
    EXPECT_EQ(e <=> d, 1);
    EXPECT_EQ(d <=> f, -1);
    EXPECT_EQ(f <=> d, 1);
    EXPECT_EQ(e <=> e, 0);
    EXPECT_EQ(e <=> f, -1);
    EXPECT_EQ(f <=> e, 1);
    EXPECT_EQ(f <=> f, 0);
}

TYPED_TEST(uint_api, arithmetic_op_assignment)
{
    TypeParam x;

    EXPECT_EQ(x += 11, 11);
    EXPECT_EQ(x -= 4, 7);
    EXPECT_EQ(x *= 2, 14);
    EXPECT_EQ(x %= 8, 6);
    EXPECT_EQ(x /= 3, 2);

    EXPECT_EQ(x += x, 4);
    EXPECT_EQ(x -= x, 0);
    EXPECT_EQ(x += uint128{3}, 3);
    EXPECT_EQ(x *= 3u, 9);
    EXPECT_EQ(x /= x, 1);
    EXPECT_EQ(x %= x, 0);
}

TYPED_TEST(uint_api, bitwise_op_assignment)
{
    TypeParam x;

    EXPECT_EQ(x |= 0b1011, 0b1011);
    EXPECT_EQ(x &= 0b0110, 0b0010);
    EXPECT_EQ(x ^= 0b1110, 0b1100);
    EXPECT_EQ(x >>= 2, 0b0011);
    EXPECT_EQ(x <<= 1, 0b0110);

    x = 0;
    EXPECT_EQ(x |= uint128{0b1011}, 0b1011);
    EXPECT_EQ(x &= uint128{0b0110}, 0b0010);
    EXPECT_EQ(x ^= uint128{0b1110}, 0b1100);
    EXPECT_EQ(x >>= uint128{2}, 0b0011);
    EXPECT_EQ(x <<= uint128{1}, 0b0110);

    EXPECT_EQ(x |= x, x);
    EXPECT_EQ(x &= x, x);
    EXPECT_EQ(x ^= x, 0);
    EXPECT_EQ(x |= 1, 1);
    EXPECT_EQ(x <<= x, 2);
    EXPECT_EQ(x >>= x, 0);
}

TYPED_TEST(uint_api, explicit_conversion_to_smaller_uint)
{
    if constexpr (TypeParam::num_bits > 128)
    {
        using SmallerType = intx::uint<TypeParam::num_bits - 64>;
        static_assert(static_cast<SmallerType>(TypeParam{1}) == 1);

        TypeParam x;
        for (size_t i = 0; i < TypeParam::num_words; ++i)
            x[i] = i + 1;

        const auto smaller = static_cast<SmallerType>(x);
        for (size_t i = 0; i < SmallerType::num_words; ++i)
        {
            EXPECT_EQ(smaller[i], i + 1);
        }
    }
}

TYPED_TEST(uint_api, explicit_conversion_to_integral_type)
{
    static_assert(
        static_cast<uint32_t>(TypeParam{0x0102030405060708, 0xffffffffffffffff}) == 0x05060708);

    TypeParam x;
    x[0] = 3;
    x[1] = 0xffffffffffffffff;

    TypeParam y;
    y[0] = 0xfffffffffffffffe;
    y[1] = 0xffffffffffffffff;

    EXPECT_EQ(static_cast<signed char>(x), 3);
    EXPECT_EQ(static_cast<signed char>(y), -2);
    EXPECT_EQ(static_cast<unsigned char>(x), 3);
    EXPECT_EQ(static_cast<unsigned char>(y), 0xfe);

    EXPECT_EQ(static_cast<signed short>(x), 3);
    EXPECT_EQ(static_cast<signed short>(y), -2);
    EXPECT_EQ(static_cast<unsigned short>(x), 3);
    EXPECT_EQ(static_cast<unsigned short>(y), 0xfffe);

    EXPECT_EQ(static_cast<signed int>(x), 3);
    EXPECT_EQ(static_cast<signed int>(y), -2);
    EXPECT_EQ(static_cast<unsigned int>(x), 3u);
    EXPECT_EQ(static_cast<unsigned int>(y), 0xfffffffe);

    EXPECT_EQ(static_cast<signed long>(x), 3);
    EXPECT_EQ(static_cast<signed long>(y), -2);
    EXPECT_EQ(static_cast<unsigned long>(x), 3u);
    EXPECT_EQ(static_cast<unsigned long>(y), std::numeric_limits<unsigned long>::max() - 1);

    EXPECT_EQ(static_cast<signed long long>(x), 3);
    EXPECT_EQ(static_cast<signed long long>(y), -2);
    EXPECT_EQ(static_cast<unsigned long long>(x), 3u);
    EXPECT_EQ(static_cast<unsigned long long>(y), 0xfffffffffffffffe);
}
