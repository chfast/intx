// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using intx::uint256;

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
