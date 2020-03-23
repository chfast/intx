// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div4.hpp"

namespace intx
{
namespace experimental
{
inline uint128 reciprocal_4by2(uint128 d) noexcept
{
    const auto reciprocal = reciprocal_3by2(d);

    const auto x1 = udivrem_3by2(~d.hi, ~d.lo, ~uint64_t{0}, d, reciprocal);
    const auto x2 = udivrem_3by2(x1.rem.hi, x1.rem.lo, ~uint64_t{0}, d, reciprocal);

    return {x1.quot, x2.quot};
}

div_result<uint128> udivrem_4by2(const uint256& u, uint128 d, uint128 v) noexcept
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

div_result<uint128> udivrem_4by2(const uint256& u, uint128 d) noexcept
{
    const auto v = reciprocal_4by2(d);
    return udivrem_4by2(u, d, v);
}

inline uint128 reciprocal_6by4(const uint256& d) noexcept
{
    auto v = reciprocal_4by2(d.hi);
    auto p = d.hi * v;
    p += d.lo;
    if (p < d.lo)
    {
        --v;
        if (p >= d.hi)
        {
            --v;
            p -= d.hi;
        }
        p -= d.hi;
    }

    const auto t = umul(v, d.lo);

    p += t.hi;
    if (p < t.hi)
    {
        --v;
        if (uint256{p, t.lo} >= d)
            --v;
    }
    return v;
}

div_result<uint128, uint256> udivrem_6by4(const uint64_t* u, const uint256& d, uint128 v) noexcept
{
    const uint128 u2{u[5], u[4]};
    const uint128 u1{u[3], u[2]};
    const uint128 u0{u[1], u[0]};

    auto q = umul(v, u2);
    q += uint256{u2, u1};

    auto r1 = u1 - q.hi * d.hi;

    auto t = umul(d.lo, q.hi);

    auto r = uint256{r1, u0} - t - d;
    r1 = r.hi;

    ++q.hi;

    if (r1 >= q.lo)
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

div_result<uint128, uint256> udivrem_6by4(const uint64_t* u, const uint256& d) noexcept
{
    return udivrem_6by4(u, d, reciprocal_6by4(d));
}

}  // namespace experimental
}  // namespace intx