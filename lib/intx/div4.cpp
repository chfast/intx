// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div4.hpp"

namespace intx
{
uint128 udivrem_by2(uint64_t u[], int len, uint128 d) noexcept;
void udivrem_knuth(uint64_t q[], uint64_t u[], int ulen, const uint64_t d[], int dlen) noexcept;

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

uint128 reciprocal_6by4(const uint256& d) noexcept
{
    const auto d1 = ~d.hi;
    const auto d0 = ~d.lo;
    uint64_t u[6]{~uint64_t{0}, ~uint64_t{0}, d0.lo, d0.hi, d1.lo, d1.hi};

    uint128 q;
    udivrem_knuth(as_words(q), u, 6, as_words(d), 4);
    return q;
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