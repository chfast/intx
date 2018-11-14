// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

using namespace intx;

void static_test_comparison()
{
    constexpr uint128 zero;
    constexpr uint128 zer0 = 0;
    constexpr uint128 one = 1;

    static_assert(zero == 0, "");
    static_assert(zero != 1, "");
    static_assert(one > 0, "");
    static_assert(one >= 0, "");
    static_assert(zero >= 0, "");
    static_assert(zero < 1, "");
    static_assert(zero <= 1, "");
    static_assert(zero <= 0, "");

    static_assert(zero == zer0, "");
    static_assert(zero != one, "");
    static_assert(one > zero, "");
    static_assert(one >= zero, "");
    static_assert(zero >= zer0, "");
    static_assert(zero < one, "");
    static_assert(zero <= one, "");
    static_assert(zero <= zer0, "");
}

void static_test_bitwise_operators()
{
    constexpr uint128 x{0x5555555555555555, 0x5555555555555555};
    constexpr uint128 y{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa};
    constexpr uint128 one = 1;
    constexpr uint128 zero = 0;

    static_assert((x | one) == x, "");
    static_assert((y | one) == uint128{0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaab}, "");

    static_assert((x & one) == one, "");
    static_assert((y & one) == zero, "");

    static_assert((x ^ zero) == x, "");
    static_assert((x ^ one) == uint128{0x5555555555555555, 0x5555555555555554}, "");

    static_assert(~x == y, "");
}

void static_test_arith()
{
    constexpr uint128 a = 0x8000000000000000;
    constexpr auto s = a + a;
    static_assert(s == uint128{1, 0}, "");
    static_assert(s - a == a, "");
    static_assert(s - 0 == s, "");
    static_assert(s + 0 == s, "");
    static_assert(-uint128(1) == uint128{0xffffffffffffffff, 0xffffffffffffffff}, "");
}