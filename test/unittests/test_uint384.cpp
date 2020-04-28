// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <gtest/gtest.h>
#include <intx/uint384.hpp>

using namespace intx;

TEST(uint384, add)
{
    const auto a = uint384(0xabde83343278989432789432cde0023131963478fdca_u512);
    const auto b = uint384(
        0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe_u512);
    const auto expected = uint384{
        0xfefefefefefefefefefefefefefefefefefefefefefefefefeffaadd82333177979331779331ccdf013030953377fcc8_u512};
    const auto s = a + b;
    EXPECT_EQ(s, expected);
    EXPECT_EQ(s - a, b);
    EXPECT_EQ(s - b, a);
}

TEST(uint384, mul)
{
    const auto a = uint384(0xabde83343278989432789432cde0023131963478fdca_u512);
    const auto b = uint384(
        0x7fefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe_u512);
    const auto expected = uint384{
        0x5e0b6f5555555555555555555555555555555555555555555554aa235d2f6551aa473d29867c13cf8d60915e56463a6c_u512};
    EXPECT_EQ(a * b, expected);
}

TEST(uint384, div)
{
    const auto a = uint384(
        0x5e0b6f5555555555555555555555555555555555555555555554aa235d2f6551aa473d29867c13cf8d60915e56463a6c_u512);
    const auto b = uint384(0x11abde83343278989432789432cde0023131963478fdca_u512);
    const auto expected = uint384{0x55265f1c67a8c76439e8309188072fbab33c1c849aec34dd975_u512};
    EXPECT_EQ(a / b, expected);
}
