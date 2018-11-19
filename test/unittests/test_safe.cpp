// Copyright 2017 Pawel Bylica
// Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)

#include <intx/safe.hpp>
#include <gtest/gtest.h>

using namespace intx;

TEST(safe_int, init)
{
    safe_int a;
    EXPECT_EQ(a, 0);
    EXPECT_TRUE(a.normal());

    safe_int b = 0;
    EXPECT_EQ(b, 0);
    EXPECT_TRUE(a.normal());

    a = -1;
    EXPECT_EQ(a, -1);
    EXPECT_TRUE(a.normal());
}

TEST(safe_int, add)
{
    safe_int a = 1;
    safe_int b = -1;

    auto s = a + b;
    EXPECT_EQ(s, 0);
    EXPECT_TRUE(s.normal());

    a = std::numeric_limits<int>::max();
    b = 1;
    s = a + b;
    EXPECT_FALSE(s.normal());
    s = 0;
    EXPECT_TRUE(s.normal());
    s = b + a;
    EXPECT_FALSE(s.normal());

    b = -1;
    s = a + b;
    EXPECT_EQ(s, a.value() - 1);
    EXPECT_TRUE(s.normal());
    s = b + a;
    EXPECT_TRUE(s.normal());

    b = 0;
    s = a + b;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.normal());
    s = b + a;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.normal());

    a = std::numeric_limits<int>::min();
    b = -1;
    s = a + b;
    EXPECT_FALSE(s.normal());
    s = b + a;
    EXPECT_FALSE(s.normal());

    b = 1;
    s = a + b;
    EXPECT_TRUE(s.normal());
    s = b + a;
    EXPECT_TRUE(s.normal());

    b = 0;
    s = a + b;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.normal());
    s = b + a;
    EXPECT_EQ(s, a);
    EXPECT_TRUE(s.normal());

    a = std::numeric_limits<int>::min();
    b = std::numeric_limits<int>::min();
    s = a + b;
    EXPECT_EQ(s.get_status(), status::minus_infinity);
    s = b + a;
    EXPECT_EQ(s.get_status(), status::minus_infinity);
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

TEST(safe_int, compare_plus_infinities)
{
    auto inf = 1 + safe_int{std::numeric_limits<int>::max()};

    bool f = false;
    EXPECT_THROW(f = inf == inf, intx::bad_operation);
    EXPECT_THROW(f = inf != inf, intx::bad_operation);
    EXPECT_THROW(f = inf < inf, intx::bad_operation);
    EXPECT_THROW(f = inf <= inf, intx::bad_operation);
    EXPECT_THROW(f = inf >= inf, intx::bad_operation);
    EXPECT_THROW(f = inf > inf, intx::bad_operation);
    (void)f;
}