// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <gtest/gtest.h>
#include <intx/int128.hpp>

using namespace intx;

static_assert(clz_generic(uint32_t{0}) == 32, "");
static_assert(clz_generic(uint32_t{1}) == 31, "");
static_assert(clz_generic(uint32_t{3}) == 30, "");
static_assert(clz_generic(uint32_t{9}) == 28, "");

static_assert(clz_generic(uint64_t{0}) == 64, "");
static_assert(clz_generic(uint64_t{1}) == 63, "");
static_assert(clz_generic(uint64_t{3}) == 62, "");
static_assert(clz_generic(uint64_t{9}) == 60, "");


TEST(builtins, clz64_single_one)
{
    for (unsigned i = 0; i <= 63; ++i)
    {
        const auto input = (uint64_t{1} << 63) >> i;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz64_two_ones)
{
    for (unsigned i = 0; i <= 63; ++i)
    {
        const auto input = ((uint64_t{1} << 63) >> i) | 1;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz32_single_one)
{
    for (unsigned i = 0; i <= 31; ++i)
    {
        const auto input = (uint32_t{1} << 31) >> i;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz32_two_ones)
{
    for (unsigned i = 0; i <= 31; ++i)
    {
        const auto input = ((uint32_t{1} << 31) >> i) | 1;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz_zero)
{
    EXPECT_EQ(clz(uint32_t{0}), 32u);
    EXPECT_EQ(clz_generic(uint32_t{0}), 32u);
    EXPECT_EQ(clz(uint64_t{0}), 64u);
    EXPECT_EQ(clz_generic(uint64_t{0}), 64u);
}

namespace
{
constexpr int func() noexcept
{
    return is_constant_evaluated() ? 1 : 2;
}
}  // namespace

TEST(builtins, is_constant_evaluated)
{
    constexpr auto is_constexpr_true = is_constant_evaluated();
    EXPECT_TRUE(is_constexpr_true);
    constexpr auto constexpr_func_res = func();
    EXPECT_EQ(constexpr_func_res, 1);

    auto is_constexpr_false = is_constant_evaluated();
    auto nonconstexpr_func_res = func();

#if (defined(__clang__) && __clang_major__ >= 9) || (defined(__GNUC__) && __GNUC__ >= 9) || \
    (defined(_MSC_VER) && _MSC_VER >= 1925)
    EXPECT_FALSE(is_constexpr_false);
    EXPECT_EQ(nonconstexpr_func_res, 2);
#else
    EXPECT_TRUE(is_constexpr_false);
    EXPECT_EQ(nonconstexpr_func_res, 1);
#endif
}
