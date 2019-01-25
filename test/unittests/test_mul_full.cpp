// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/mul_full.h>
#include <intx/int128.hpp>

#include "../utils/random.hpp"
#include <gtest/gtest.h>

TEST(mul_full, random)
{
    auto inputs = gen_uniform_seq(10000);

    for (size_t i = 1; i < inputs.size(); ++i)
    {
        auto x = inputs[i - 1];
        auto y = inputs[i];

        auto generic = mul_full_64_generic(x, y);
        auto native = mul_full_64_native(x, y);
        auto int128_generic = intx::umul_generic(x, y);
        auto int128_best = intx::umul(x, y);

        EXPECT_EQ(generic.hi, native.hi) << x << " x " << y;
        EXPECT_EQ(generic.lo, native.lo) << x << " x " << y;
        EXPECT_EQ(int128_generic.hi, native.hi) << x << " x " << y;
        EXPECT_EQ(int128_generic.lo, native.lo) << x << " x " << y;
        EXPECT_EQ(int128_best.hi, native.hi) << x << " x " << y;
        EXPECT_EQ(int128_best.lo, native.lo) << x << " x " << y;
    }
}
