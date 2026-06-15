// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"

using namespace intx;

TYPED_TEST(sint_test, comparison)
{
    // Signed order: min < ... < -1 < 0 < 1 < ... < max
    constexpr auto zero = TypeParam{};
    constexpr auto one = TypeParam{1};
    constexpr auto neg_one = -TypeParam{1};
    constexpr auto min = TypeParam{1} << (TypeParam::num_bits - 1);  // 100...0, most negative
    constexpr auto max = ~min;                                       // 011...1, most positive

    EXPECT_EQ(zero, zero);
    EXPECT_EQ(one, one);
    EXPECT_EQ(neg_one, neg_one);
    EXPECT_EQ(min, min);
    EXPECT_EQ(max, max);

    EXPECT_NE(zero, one);
    EXPECT_NE(zero, neg_one);
    EXPECT_NE(min, max);

    // Negative values are less than positive/zero
    EXPECT_LT(min, neg_one);
    EXPECT_LT(min, zero);
    EXPECT_LT(min, one);
    EXPECT_LT(min, max);
    EXPECT_LT(neg_one, zero);
    EXPECT_LT(neg_one, one);
    EXPECT_LT(neg_one, max);
    EXPECT_LT(zero, one);
    EXPECT_LT(zero, max);
    EXPECT_LT(one, max);

    EXPECT_GT(max, one);
    EXPECT_GT(max, zero);
    EXPECT_GT(max, neg_one);
    EXPECT_GT(max, min);
    EXPECT_GT(one, zero);
    EXPECT_GT(one, neg_one);
    EXPECT_GT(zero, neg_one);
    EXPECT_GT(neg_one, min);

    EXPECT_LE(min, min);
    EXPECT_LE(min, zero);
    EXPECT_LE(neg_one, neg_one);
    EXPECT_LE(neg_one, zero);
    EXPECT_LE(zero, zero);
    EXPECT_LE(zero, one);
    EXPECT_LE(max, max);

    EXPECT_GE(max, max);
    EXPECT_GE(max, zero);
    EXPECT_GE(one, zero);
    EXPECT_GE(zero, zero);
    EXPECT_GE(zero, neg_one);
    EXPECT_GE(neg_one, neg_one);
    EXPECT_GE(neg_one, min);
    EXPECT_GE(min, min);
}

TYPED_TEST(sint_test, negation_overflow)
{
    // -INT_MIN == INT_MIN (two's complement overflow)
    constexpr auto min = TypeParam{1} << (TypeParam::num_bits - 1);
    EXPECT_EQ(-min, min);

    EXPECT_EQ(-TypeParam{}, TypeParam{});
    EXPECT_EQ(-(-TypeParam{1}), TypeParam{1});
}

TYPED_TEST(sint_test, arithmetic)
{
    constexpr auto zero = TypeParam{};
    constexpr auto one = TypeParam{1};
    constexpr auto neg_one = -TypeParam{1};
    constexpr auto min = TypeParam{1} << (TypeParam::num_bits - 1);
    constexpr auto max = ~min;

    EXPECT_EQ(zero + zero, zero);
    EXPECT_EQ(one + zero, one);
    EXPECT_EQ(neg_one + one, zero);
    EXPECT_EQ(neg_one + neg_one, -TypeParam{2});
    EXPECT_EQ(max + one, min);  // INT_MAX + 1 wraps to INT_MIN

    EXPECT_EQ(zero - zero, zero);
    EXPECT_EQ(one - one, zero);
    EXPECT_EQ(zero - one, neg_one);
    EXPECT_EQ(neg_one - neg_one, zero);
    EXPECT_EQ(min - one, max);  // INT_MIN - 1 wraps to INT_MAX

    EXPECT_EQ(zero * one, zero);
    EXPECT_EQ(one * one, one);
    EXPECT_EQ(neg_one * one, neg_one);
    EXPECT_EQ(neg_one * neg_one, one);
    EXPECT_EQ(TypeParam{3} * neg_one, -TypeParam{3});
    EXPECT_EQ(-TypeParam{3} * TypeParam{2}, -TypeParam{6});
}

TYPED_TEST(sint_test, assignment_operators)
{
    auto x = TypeParam{5};
    x += TypeParam{3};
    EXPECT_EQ(x, TypeParam{8});
    x -= TypeParam{3};
    EXPECT_EQ(x, TypeParam{5});
    x *= TypeParam{2};
    EXPECT_EQ(x, TypeParam{10});
    x /= TypeParam{3};
    EXPECT_EQ(x, TypeParam{3});
    x %= TypeParam{2};
    EXPECT_EQ(x, TypeParam{1});

    auto y = TypeParam{3};
    y |= TypeParam{5};
    EXPECT_EQ(y, TypeParam{7});
    y &= TypeParam{5};
    EXPECT_EQ(y, TypeParam{5});
    y ^= TypeParam{3};
    EXPECT_EQ(y, TypeParam{6});

    auto z = TypeParam{2};
    z <<= TypeParam{2};
    EXPECT_EQ(z, TypeParam{8});
    z >>= TypeParam{1};
    EXPECT_EQ(z, TypeParam{4});

    // Arithmetic right shift via assignment
    auto w = -TypeParam{8};
    w >>= TypeParam{1};
    EXPECT_EQ(w, -TypeParam{4});
}

TYPED_TEST(sint_test, division)
{
    // Truncation toward zero
    EXPECT_EQ(TypeParam{7} / TypeParam{3}, TypeParam{2});
    EXPECT_EQ(TypeParam{7} % TypeParam{3}, TypeParam{1});
    EXPECT_EQ(-TypeParam{7} / TypeParam{3}, -TypeParam{2});
    EXPECT_EQ(-TypeParam{7} % TypeParam{3}, -TypeParam{1});
    EXPECT_EQ(TypeParam{7} / -TypeParam{3}, -TypeParam{2});
    EXPECT_EQ(TypeParam{7} % -TypeParam{3}, TypeParam{1});
    EXPECT_EQ(-TypeParam{7} / -TypeParam{3}, TypeParam{2});
    EXPECT_EQ(-TypeParam{7} % -TypeParam{3}, -TypeParam{1});

    EXPECT_EQ(TypeParam{42} / TypeParam{1}, TypeParam{42});
    EXPECT_EQ(-TypeParam{42} / TypeParam{1}, -TypeParam{42});
    EXPECT_EQ(TypeParam{42} % TypeParam{42}, TypeParam{});

    EXPECT_EQ(TypeParam{} / TypeParam{7}, TypeParam{});
    EXPECT_EQ(TypeParam{} % TypeParam{7}, TypeParam{});

    EXPECT_EQ(TypeParam{3} / TypeParam{7}, TypeParam{});
    EXPECT_EQ(-TypeParam{3} / TypeParam{7}, TypeParam{});
    EXPECT_EQ(TypeParam{3} % TypeParam{7}, TypeParam{3});
    EXPECT_EQ(-TypeParam{3} % TypeParam{7}, -TypeParam{3});
}

TYPED_TEST(sint_test, arithmetic_right_shift)
{
    constexpr auto neg_one = ~TypeParam{};                                // -1, all ones
    constexpr auto min = TypeParam{1} << (TypeParam::num_bits - 1);       // 100...0
    constexpr auto min_shr1 = TypeParam{3} << (TypeParam::num_bits - 2);  // 110...0

    // Negative: fill with 1s
    EXPECT_EQ(neg_one >> 1u, neg_one);
    EXPECT_EQ(neg_one >> uint64_t{TypeParam::num_bits - 1}, neg_one);
    EXPECT_EQ(min >> 1u, min_shr1);
    EXPECT_EQ(min >> uint64_t{TypeParam::num_bits - 1}, neg_one);

    // Positive: fill with 0s
    EXPECT_EQ(TypeParam{8} >> 1u, TypeParam{4});
    EXPECT_EQ(TypeParam{1} >> 1u, TypeParam{});

    // Overflow (shift >= N): return all sign bits
    EXPECT_EQ(neg_one >> uint64_t{TypeParam::num_bits}, neg_one);
    EXPECT_EQ(TypeParam{1} >> uint64_t{TypeParam::num_bits}, TypeParam{});
    EXPECT_EQ(min >> uint64_t{TypeParam::num_bits}, neg_one);
}

TYPED_TEST(sint_test, left_shift)
{
    EXPECT_EQ(TypeParam{1} << 1u, TypeParam{2});
    EXPECT_EQ(TypeParam{1} << 0u, TypeParam{1});

    // Overflow: returns 0
    EXPECT_EQ(TypeParam{1} << uint64_t{TypeParam::num_bits}, TypeParam{});
    EXPECT_EQ(~TypeParam{} << uint64_t{TypeParam::num_bits}, TypeParam{});
}

TYPED_TEST(sint_test, bitwise)
{
    constexpr auto zero = TypeParam{};
    constexpr auto neg_one = ~TypeParam{};
    constexpr auto one = TypeParam{1};

    EXPECT_EQ(zero & neg_one, zero);
    EXPECT_EQ(neg_one & neg_one, neg_one);
    EXPECT_EQ(zero | neg_one, neg_one);
    EXPECT_EQ(zero | zero, zero);
    EXPECT_EQ(neg_one ^ neg_one, zero);
    EXPECT_EQ(zero ^ neg_one, neg_one);
    EXPECT_EQ(~zero, neg_one);
    EXPECT_EQ(~neg_one, zero);
    EXPECT_EQ(one & neg_one, one);
    EXPECT_EQ(one | neg_one, neg_one);
    EXPECT_EQ(one ^ neg_one, ~one);
}

TYPED_TEST(sint_test, convert_to_bool)
{
    constexpr auto min = TypeParam{1} << (TypeParam::num_bits - 1);
    EXPECT_FALSE((TypeParam{}));
    EXPECT_TRUE((TypeParam{1}));
    EXPECT_TRUE((-TypeParam{1}));
    EXPECT_TRUE(min);
}

// int128-specific static and runtime tests

namespace static_test_sint128_comparison
{
constexpr int128 zero;
constexpr int128 one = 1;
constexpr int128 neg_one = -int128{1};
constexpr int128 min = int128{1} << 127;
constexpr int128 max = ~min;

static_assert(zero == 0);
static_assert(zero != 1);
static_assert(one > 0);
static_assert(zero < 1);

static_assert(neg_one < zero);
static_assert(neg_one < one);
static_assert(min < neg_one);
static_assert(min < zero);
static_assert(max > zero);
static_assert(max > neg_one);
static_assert(max > min);

static_assert((int128{1} <=> int128{2}) == std::strong_ordering::less);
static_assert((int128{2} <=> int128{1}) == std::strong_ordering::greater);
static_assert((int128{1} <=> int128{1}) == std::strong_ordering::equal);
static_assert((neg_one <=> zero) == std::strong_ordering::less);
static_assert((zero <=> neg_one) == std::strong_ordering::greater);
}  // namespace static_test_sint128_comparison

namespace static_test_sint128_arith
{
constexpr int128 one = 1;
constexpr int128 neg_one = -int128{1};

static_assert(neg_one + one == 0);
static_assert(one - one == 0);  // NOLINT(misc-redundant-expression): part of the test
static_assert(neg_one * neg_one == one);
static_assert(neg_one * one == neg_one);
static_assert(int128{3} * int128{4} == int128{12});
static_assert(-int128{3} * int128{4} == -int128{12});
static_assert((int128{1} << 127) + (-int128{1} << 127) == 0);
}  // namespace static_test_sint128_arith

TEST(sint128, comparison)
{
    constexpr auto neg_one = -int128{1};
    constexpr auto min = int128{1} << 127;
    constexpr auto max = ~min;

    EXPECT_LT(neg_one, int128{0});
    EXPECT_LT(min, neg_one);
    EXPECT_GT(max, int128{0});
    EXPECT_GT(int128{0}, neg_one);
    EXPECT_GT(max, min);
}

TEST(sint128, negation)
{
    constexpr auto min = int128{1} << 127;
    EXPECT_EQ(-min, min);
    EXPECT_EQ(-int128{0}, int128{0});
    EXPECT_EQ(-(-int128{42}), int128{42});
    EXPECT_EQ(-int128{1}, ~int128{0});
}

TEST(sint128, division)
{
    // Use the same values as the sdivrem test in test_int128.cpp.
    // Read words from the uint128 literals to avoid manual hex decomposition errors.
    constexpr auto xu = 0x83017fa6deecda0063b1977_u128;
    constexpr auto yu = 0x1bc83504ea8f7_u128;
    constexpr int128 x{xu[0], xu[1]};
    constexpr int128 y{yu[0], yu[1]};

    EXPECT_EQ(x / y, int128{0x4b729f5338f});
    EXPECT_EQ(x % y, int128{0x13e5e3b3e827e});

    EXPECT_EQ((-x) / (-y), int128{0x4b729f5338f});
    EXPECT_EQ((-x) % (-y), -int128{0x13e5e3b3e827e});

    EXPECT_EQ((-x) / y, -int128{0x4b729f5338f});
    EXPECT_EQ((-x) % y, -int128{0x13e5e3b3e827e});

    EXPECT_EQ(x / (-y), -int128{0x4b729f5338f});
    EXPECT_EQ(x % (-y), int128{0x13e5e3b3e827e});
}

TEST(sint128, arithmetic_right_shift)
{
    constexpr auto neg_one = ~int128{0};
    constexpr auto min = int128{1} << 127;

    static_assert((neg_one >> 1) == neg_one);
    static_assert((neg_one >> 127) == neg_one);
    static_assert((neg_one >> 128) == neg_one);
    static_assert((int128{4} >> 1) == int128{2});
    static_assert((min >> 127) == neg_one);

    EXPECT_EQ(neg_one >> 1, neg_one);
    EXPECT_EQ(neg_one >> 127, neg_one);
    EXPECT_EQ(neg_one >> 128, neg_one);
    EXPECT_EQ(int128{4} >> 1, int128{2});
    EXPECT_EQ(min >> 1, int128{3} << 126);
    EXPECT_EQ(min >> 127, neg_one);
    EXPECT_EQ(min >> 128, neg_one);
}
