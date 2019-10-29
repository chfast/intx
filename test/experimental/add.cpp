// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
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

namespace intx
{
namespace experimental
{
uint256 add_recursive(const uint256& a, const uint256& b) noexcept
{
    const auto ll = a.lo.lo + b.lo.lo;
    const auto l_carry = ll < a.lo.lo;
    const auto lh = a.lo.hi + b.lo.hi + l_carry;

    const bool lo_carry = (lh < a.lo.hi) | ((lh == a.lo.hi) & l_carry);

    const auto tl = a.hi.lo + b.hi.lo;
    const auto t_carry = tl < a.hi.lo;
    const auto th = a.hi.hi + b.hi.hi + t_carry;

    const auto hl = tl + lo_carry;
    const auto hl_carry = hl < tl;
    const auto hh = th + hl_carry;

    return {{hh, hl}, {lh, ll}};
}

uint256 add_waterflow(const uint256& a, const uint256& b) noexcept
{
    const auto ll = a.lo.lo + b.lo.lo;
    auto carry = ll < a.lo.lo;

    auto lh = a.lo.hi + b.lo.hi;
    auto k1 = lh < a.lo.hi;
    lh += carry;
    auto k2 = lh < uint64_t{carry};
    carry = k1 | k2;

    auto hl = a.hi.lo + b.hi.lo;
    k1 = hl < a.hi.lo;
    hl += carry;
    k2 = hl < uint64_t{carry};
    carry = k1 | k2;

    auto hh = a.hi.hi + b.hi.hi;
    hh += carry;

    return {{hh, hl}, {lh, ll}};
}
}  // namespace experimental
}  // namespace intx
