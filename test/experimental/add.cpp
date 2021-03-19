// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

/// @file
/// In this file we have 256-bit add procedures to inspect how good are
/// compilers at optimizing these.

#if INTX_EXPERIMENTAL
    #include "add.hpp"
#else
    #include <cstdint>

struct uint128
{
    uint64_t lo;
    uint64_t hi;
};

struct uint256
{
    uint128 lo;
    uint128 hi;
};
#endif

struct uint192
{
    uint64_t lo;
    uint64_t mi;
    uint64_t hi;
};

namespace intx
{
namespace experimental
{
#ifndef INTX_EXPERIMENTAL
bool uaddo(uint64_t al, uint64_t ah, uint64_t bl, uint64_t bh, uint128* res) noexcept
{
    const auto ll = al + bl;
    auto carry = ll < al;

    auto s = ah + bh;
    auto k1 = s < ah;
    auto lh = s + carry;
    auto k2 = lh < s;
    carry = k1 | k2;

    *res = uint128{lh, ll};
    return carry;
}

uint192 add_waterfall(
    uint64_t all, uint64_t alh, uint64_t ahl, uint64_t bll, uint64_t blh, uint64_t bhl) noexcept
{
    const auto ll = all + bll;
    auto carry = ll < all;

    auto s = alh + blh;
    auto k1 = s < alh;
    auto lh = s + carry;
    auto k2 = lh < s;
    carry = k1 | k2;

    auto hl = ahl + bhl + carry;

    return {hl, lh, ll};
}
#endif

uint256 add_recursive(const uint256& a, const uint256& b) noexcept
{
    uint128 lo;
    bool lo_carry;
    {
        const auto l = a[0] + b[0];
        const auto l_carry = l < a[0];
        const auto t = a[1] + b[1];
        const auto carry1 = t < a[1];
        const auto h = t + l_carry;
        const auto carry2 = h < t;
        lo = uint128{h, l};
        lo_carry = carry1 || carry2;
    }

    uint128 tt;
    {
        const auto l = a[2] + b[2];
        const auto l_carry = l < a[2];
        const auto t = a[3] + b[3];
        const auto h = t + l_carry;
        tt = uint128{h, l};
    }

    uint128 hi;
    {
        const auto l = tt[0] + lo_carry;
        const auto l_carry = l < tt[0];
        const auto h = tt[1] + l_carry;
        hi = uint128{h, l};
    }

    return {hi, lo};
}

uint256 add_waterflow(const uint256& a, const uint256& b) noexcept
{
    const auto ll = a[0] + b[0];
    auto carry = ll < a[0];

    auto lh = a[1] + b[1];
    auto k1 = lh < a[1];
    lh += carry;
    auto k2 = lh < uint64_t{carry};
    carry = k1 | k2;

    auto hl = a[2] + b[2];
    k1 = hl < a[2];
    hl += carry;
    k2 = hl < uint64_t{carry};
    carry = k1 | k2;

    auto hh = a[3] + b[3];
    hh += carry;

    return {{hh, hl}, {lh, ll}};
}
}  // namespace experimental
}  // namespace intx
