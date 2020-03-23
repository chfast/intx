// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div4.hpp"

namespace intx
{
uint128 udivrem_by2(uint64_t u[], int len, uint128 d) noexcept;

namespace experimental
{
uint128 reciprocal_4by2(uint128 d) noexcept
{
    uint256 n{~d, ~uint128{0}};

    udivrem_by2(as_words(n), 4, d);

    return n.lo;
}

div_result<uint128> udivrem_4by2(uint256 u, uint128 d, uint128 v) noexcept
{
    auto q = umul(v, u.hi);
    q += u;

    ++q.hi;

    auto r = u.lo - q.hi * d;

    if (r > q.lo)
    {
        --q.hi;
        r += d;
    }

    if (r >= d)
    {
        ++q.hi;
        r -= d;
    }

    return {q.hi, r};
}

div_result<uint128> udivrem_4by2(uint256 u, uint128 d) noexcept
{
    const auto v = reciprocal_4by2(d);
    return udivrem_4by2(u, d, v);
}

}  // namespace experimental
}  // namespace intx