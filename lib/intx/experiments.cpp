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
    using u128 = unsigned __int128;

    auto d9 = uint8_t(d >> 55);
    auto v0 = uint64_t{reciprocal_table[d9]};

    auto d40 = (d >> 24) + 1;
    auto v1 = (v0 << 11) - (v0 * v0 * d40 >> 40) - 1;

    auto v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    auto d0 = d % 2;
    auto d63 = d / 2 + d0;  // ceil(d/2)
    auto e = ((v2 / 2) & -d0) - v2 * d63;
    auto mh = uint64_t((u128{v2} * e) >> 64);
    auto v3 = (v2 << 31) + (mh >> 1);

    auto mf = u128{v3} * d + d;  // full mul
    auto v3a = uint64_t(mf >> 64) + d;

    auto v4 = v3 - v3a;

    return v4;
}

uint64_t reciprocal_3by2(uint64_t d1, uint64_t d0) noexcept
{
    using u128 = unsigned __int128;

    auto v = reciprocal(d1);
    auto p = d1 * v;
    p += d0;
    if (p < d0)
    {
        --v;
        if (p >= d1)
        {
            --v;
            p -= d1;
        }
        p -= d1;
    }

    auto t = u128{v} * d0;
    auto t1 = uint64_t(t >> 64);
    auto t0 = uint64_t(t);

    p += t1;
    if (p < t1)
    {
        --v;
        if (uint128{p, t0} >= uint128{d1, d0})
            --v;
    }
    return v;
}

div_result<uint64_t> udivrem_2by1(uint64_t u1, uint64_t u0, uint64_t d, uint64_t v) noexcept
{
    using u128 = unsigned __int128;
    auto q = u128{v} * u1;
    q += (u128{u1} << 64) | u0;

    auto q1 = uint64_t(q >> 64);
    auto q0 = uint64_t(q);

    ++q1;

    auto r = u0 - q1 * d;

    if (r > q0)
    {
        --q1;
        r += d;
    }

    if (r >= d)
    {
        ++q1;
        r -= d;
    }

    return {q1, r};
}

div_result<uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint64_t d1, uint64_t d0) noexcept
{
    auto v = reciprocal_3by2(d1, d0);
    using u128 = unsigned __int128;
    auto q = u128{v} * u2;
    q += (u128{u2} << 64) | u1;

    auto q1 = uint64_t(q >> 64);
    auto q0 = uint64_t(q);

    auto r1 = u1 - q1 * d1;

    auto t = u128{d0} * q1;

    auto d = ((u128{d1} << 64) | d0);
    auto r = ((u128{r1} << 64) | u0) - t - d;
    r1 = uint64_t(r >> 64);

    ++q1;

    if (r1 >= q0)
    {
        --q1;
        r += d;
    }

    if (r >= d)
    {
        ++q1;
        r -= d;
    }

    return {q1, r};
}

uint64_t udiv_by_reciprocal(uint64_t uu, uint64_t du) noexcept
{
    using u128 = unsigned __int128;

    auto shift = __builtin_clzl(du);
    auto u = u128{uu} << shift;
    auto d = du << shift;
    auto v = reciprocal(d);

    auto u1 = uint64_t(u >> 64);
    auto u0 = uint64_t(u);
    return udivrem_2by1(u1, u0, d, v).quot;
}

}  // namespace experiments
}  // namespace intx