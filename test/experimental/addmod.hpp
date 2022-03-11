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
    const auto s = addc(x, y);
    uint<256 + 64> n = s.value;
    n[4] = s.carry;
    return udivrem(n, mod).rem;
}

[[maybe_unused, gnu::noinline]] static uint256 addmod_prenormalize(
    const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    const auto xm = x >= mod ? x % mod : x;
    const auto ym = y >= mod ? y % mod : y;

    const auto s = addc(xm, ym);
    auto sum = s.value;
    if (s.carry || s.value >= mod)
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
        auto s = subc(x, m);
        if (s.carry)
            s.value = x;

        auto t = subc(y, m);
        if (t.carry)
            t.value = y;

        s = addc(s.value, t.value);
        t = subc(s.value, m);
        return (s.carry || !t.carry) ? t.value : s.value;
    }

    const auto s = addc(x, y);
    uint<256 + 64> n = s.value;
    n[4] = s.carry;
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
        const auto xd = subc(x, mod);
        if (!xd.carry)
            xn = xd.value;

        // Normalize y in case it is bigger than mod.
        auto yn = y;
        const auto yd = subc(y, mod);
        if (!yd.carry)
            yn = yd.value;

        const auto a = addc(xn, yn);
        const auto av = a.value;
        const auto b = subc(av, mod);
        const auto bv = b.value;
        if (a.carry || !b.carry)
            return bv;
        return av;
    }

    const auto s = addc(x, y);
    uint<256 + 64> n = s.value;
    n[4] = s.carry;
    return udivrem(n, mod).rem;
}
}  // namespace intx::test
