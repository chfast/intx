// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/int128.hpp>

#include "../utils/random.hpp"
#include <gtest/gtest.h>

TEST(mul_full, random)
{
    const auto inputs = gen_uniform_seq(10000);

    for (size_t i = 1; i < inputs.size(); ++i)
    {
        auto x = inputs[i - 1];
        auto y = inputs[i];

        auto generic = intx::umul_generic(x, y);
        auto best = intx::umul(x, y);

        EXPECT_EQ(generic.hi, best.hi) << x << " x " << y;
        EXPECT_EQ(generic.lo, best.lo) << x << " x " << y;
    }
}
