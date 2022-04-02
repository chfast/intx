// intx: extended precision integer library.
// Copyright 2021 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

namespace intx::test
{
[[maybe_unused, gnu::noinline]] static uint256 addmod_public(
    const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    return addmod(x, y, mod);
}

[[maybe_unused, gnu::noinline]] static uint256 addmod_simple(
    const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    unsigned long long carry = 0;
    uint<256 + 64> n = addc(x, y, &carry);
    n[4] = carry;
    return udivrem(n, mod).rem;
}

[[maybe_unused, gnu::noinline]] static uint256 addmod_prenormalize(
    const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    const auto xm = x >= mod ? x % mod : x;
    const auto ym = y >= mod ? y % mod : y;

    unsigned long long carry = 0;
    auto sum = addc(xm, ym, &carry);
    if (carry || sum >= mod)
        sum -= mod;
    return sum;
}

[[maybe_unused, gnu::noinline]] static uint256 addmod_daosvik_v1(
    const uint256& x, const uint256& y, const uint256& m) noexcept
{
    // Fast path for m >= 2^192, with x and y at most slightly bigger than m.
    // This is always the case when x and y are already reduced modulo m.
    // Based on https://github.com/holiman/uint256/pull/86.
    if ((m[3] != 0) && (x[3] <= m[3]) && (y[3] <= m[3]))
    {
        unsigned long long carry = 0;
        auto s = subc(x, m, &carry);
        if (carry)
            s = x;

        carry = 0;
        auto t = subc(y, m, &carry);
        if (carry)
            t = y;

        carry = 0;
        s = addc(s, t, &carry);

        unsigned long long carry2 = 0;
        t = subc(s, m, &carry2);

        return (carry || !carry2) ? t : s;
    }

    unsigned long long carry = 0;
    uint<256 + 64> n = addc(x, y, &carry);
    n[4] = carry;
    return udivrem(n, m).rem;
}

[[maybe_unused, gnu::noinline]] static uint256 addmod_daosvik_v2(
    const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    // Fast path for m >= 2^192, with x and y at most slightly bigger than m.
    // This is always the case when x and y are already reduced modulo m.
    // Based on https://github.com/holiman/uint256/pull/86.
    if ((mod[3] != 0) && (x[3] <= mod[3]) && (y[3] <= mod[3]))
    {
        // Normalize x in case it is bigger than mod.
        auto xn = x;
        unsigned long long carry = 0;
        const auto xd = subc(x, mod, &carry);
        if (!carry)
            xn = xd;

        // Normalize y in case it is bigger than mod.
        auto yn = y;
        carry = 0;
        const auto yd = subc(y, mod, &carry);
        if (!carry)
            yn = yd;

        carry = 0;
        const auto av = addc(xn, yn, &carry);

        unsigned long long carry2 = 0;
        const auto bv = subc(av, mod, &carry2);
        if (carry || !carry2)
            return bv;
        return av;
    }

    unsigned long long carry = 0;
    uint<256 + 64> n = addc(x, y, &carry);
    n[4] = carry;
    return udivrem(n, mod).rem;
}
}  // namespace intx::test
