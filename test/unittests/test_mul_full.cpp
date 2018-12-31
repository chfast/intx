// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/mul_full.h>

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

        EXPECT_EQ(generic.hi, native.hi) << x << " x " << y;
        EXPECT_EQ(generic.lo, native.lo) << x << " x " << y;
    }
}
