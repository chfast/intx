// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using intx::uint128;

TEST(uint128, add)
{
    uint128 a = 1;
    uint128 b = 2;
    EXPECT_EQ(a + b, 3);
}
