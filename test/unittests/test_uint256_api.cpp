// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace intx;

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

using types = testing::Types<uint256, uint512>;
TYPED_TEST_CASE(uint_api, types);

TYPED_TEST(uint_api, arithmetic)
{
    auto a = int{};
    auto b = uint64_t{};
    auto c = uint128{};
    auto d = uint256{};

    auto x = TypeParam{};

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

TYPED_TEST(uint_api, comparison)
{
    auto a = int{3};
    auto b = uint64_t{5};
    auto c = uint128{7};
    auto d = uint256{11};

    auto x = TypeParam{};

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
