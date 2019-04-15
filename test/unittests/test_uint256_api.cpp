// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace intx;

TEST(uint256, add)
{
    uint256 a = 1;
    uint256 b = 2;
    EXPECT_EQ(a + b, 3);

    auto c = a + b;
    EXPECT_EQ(c, 3);
    EXPECT_EQ(c + 1, 4);

    // FIXME:
    // EXPECT_EQ(1 + c, 4);

    EXPECT_EQ(add(a, b), 3);
}

TEST(uint256, div)
{
    uint256 a = 10001;
    uint256 b = 10;

    // FIXME:
    // EXPECT_EQ(a / b, 1000);
    (void)a;
    (void)b;
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
