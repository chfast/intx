// Copyright 2017 Pawel Bylica
// Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)

#include <intx/safe.hpp>
#include <gtest/gtest.h>

using namespace intx;

TEST(safe_int, init)
{
    safe_int a;
    EXPECT_EQ(a, 0);
    EXPECT_TRUE(a.valid());

    safe_int b = 0;
    EXPECT_EQ(b, 0);
    EXPECT_TRUE(a.valid());

    a = -1;
    EXPECT_EQ(a, -1);
    EXPECT_TRUE(a.valid());
}

TEST(safe_int, add)
{
    safe_int a = 1;
    safe_int b = -1;

    auto s = a + b;
    EXPECT_EQ(s, 0);
    EXPECT_TRUE(s.valid());

    a = std::numeric_limits<int>::max();
    b = 1;
    s = a + b;
    EXPECT_FALSE(s.valid());
    s = 0;
    EXPECT_TRUE(s.valid());
    s = b + a;
    EXPECT_FALSE(s.valid());

    b = -1;
    s = a + b;
    EXPECT_EQ(s, a.value() - 1);
    EXPECT_TRUE(s.valid());
    s = b + a;
    EXPECT_TRUE(s.valid());

    b = 0;
    s = a + b;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.valid());
    s = b + a;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.valid());

    a = std::numeric_limits<int>::min();
    b = -1;
    s = a + b;
    EXPECT_FALSE(s.valid());
    s = b + a;
    EXPECT_FALSE(s.valid());

    b = 1;
    s = a + b;
    EXPECT_TRUE(s.valid());
    s = b + a;
    EXPECT_TRUE(s.valid());

    b = 0;
    s = a + b;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.valid());
    s = b + a;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.valid());
}

TEST(safe_int, compare_with_plus_infinity)
{
    safe_int h = std::numeric_limits<int>::max() / 2;

    auto a = h + h;
    EXPECT_FALSE(a == h);
    EXPECT_TRUE(a != h);
    EXPECT_FALSE(a < h);
    EXPECT_FALSE(a <= h);
    EXPECT_TRUE(a >= h);
    EXPECT_TRUE(a > h);

    auto inf = h + h + h;
    EXPECT_FALSE(inf == h);
    EXPECT_TRUE(inf != h);
    EXPECT_FALSE(inf < h);
    EXPECT_FALSE(inf <= h);
    EXPECT_TRUE(inf >= h);
    EXPECT_TRUE(inf > h);
}