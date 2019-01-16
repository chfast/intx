// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include "experiments.hpp"
#include <intx/int128.hpp>

namespace intx
{
namespace experiments
{
namespace
{
constexpr uint16_t reciprocal_table_item(uint8_t d9) noexcept
{
    return uint16_t(0x7fd00 / (0x100 | d9));
}

#define REPEAT4(x)                                                  \
    reciprocal_table_item((x) + 0), reciprocal_table_item((x) + 1), \
        reciprocal_table_item((x) + 2), reciprocal_table_item((x) + 3)

#define REPEAT32(x)                                                                         \
    REPEAT4((x) + 4 * 0), REPEAT4((x) + 4 * 1), REPEAT4((x) + 4 * 2), REPEAT4((x) + 4 * 3), \
        REPEAT4((x) + 4 * 4), REPEAT4((x) + 4 * 5), REPEAT4((x) + 4 * 6), REPEAT4((x) + 4 * 7)

#define REPEAT256()                                                                           \
    REPEAT32(32 * 0), REPEAT32(32 * 1), REPEAT32(32 * 2), REPEAT32(32 * 3), REPEAT32(32 * 4), \
        REPEAT32(32 * 5), REPEAT32(32 * 6), REPEAT32(32 * 7)

/// Reciprocal lookup table.
constexpr uint16_t reciprocal_table[] = {REPEAT256()};
}  // namespace


/// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
///
/// Based on Algorithm 2 from "Improved division by invariant integers".
uint64_t reciprocal(uint64_t d) noexcept
{
    auto d9 = uint8_t(d >> 55);
    auto v0 = uint64_t{reciprocal_table[d9]};

    auto d40 = (d >> 24) + 1;
    auto v1 = (v0 << 11) - (v0 * v0 * d40 >> 40) - 1;

    auto v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    auto d0 = d % 2;
    auto d63 = d / 2 + d0;  // ceil(d/2)
    auto e = ((v2 / 2) & -d0) - v2 * d63;
    auto mh = (uint128{v2} * e).hi;  // umulh
    auto v3 = (v2 << 31) + (mh >> 1);

    // OPT: The compiler tries a bit too much with 128 + 64 addition and ends up using subtraction.
    //      Compare with __int128.
    auto mf = uint128{v3} * d;  // full mul
    auto m = internal::optimized_add(mf, d);
    auto v3a = m.hi + d;

    auto v4 = v3 - v3a;

    return v4;
}

uint64_t reciprocal_3by2(uint128 d) noexcept
{
    auto v = reciprocal(d.hi);
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

    auto t = uint128{v} * d.lo;

    p += t.hi;
    if (p < t.hi)
    {
        --v;
        if (uint128{p, t.lo} >= d)
            --v;
    }
    return v;
}

div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept
{
    auto q = uint128{v} * u.hi;
    q = internal::optimized_add(q, u);

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

div_result<uint128> udivrem_3by2(uint64_t u2, uint64_t u1, uint64_t u0, uint128 d) noexcept
{
    auto v = reciprocal_3by2(d);
    auto q = uint128{v} * u2;
    q = internal::optimized_add(q, {u2, u1});

    auto r1 = u1 - q.hi * d.hi;

    auto t = uint128{d.lo} * q.hi;

    auto r = uint128{r1, u0} - t - d;
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

uint64_t udiv_by_reciprocal(uint64_t uu, uint64_t du) noexcept
{
    auto shift = __builtin_clzl(du);
    auto u = uint128{uu} << shift;
    auto d = du << shift;
    auto v = reciprocal(d);

    return udivrem_2by1(u, d, v).quot;
}

}  // namespace experiments
}  // namespace intx