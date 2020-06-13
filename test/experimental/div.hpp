// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

namespace intx
{
namespace experimental
{
inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    const auto u = uint128{~d, ~uint64_t{0}};
    uint64_t v;

#if _MSC_VER
    v = (u / d).lo;
#else
    uint64_t _;
    asm("divq %4" : "=d"(_), "=a"(v) : "d"(u.hi), "a"(u.lo), "g"(d));
#endif

    return v;
}

inline uint64_t reciprocal32_naive(uint64_t d64) noexcept
{
    const auto d = static_cast<uint32_t>(d64 >> 32);
    const auto uh = ~d;
    const auto ul = ~uint32_t{0};

    uint32_t v;
    const auto u = (uint64_t{uh} << 32) | ul;
    v = static_cast<uint32_t>(u / d);
    return v;
}

inline uint64_t reciprocal32_asm(uint64_t d64) noexcept
{
#if _MSC_VER
    return reciprocal32_naive(d64);
#else
    const auto d = static_cast<uint32_t>(d64 >> 32);
    const auto uh = ~d;
    const auto ul = ~uint32_t{0};

    uint32_t _, v;
    asm("divl %4" : "=d"(_), "=a"(v) : "d"(uh), "a"(ul), "r"(d));
    return v;
#endif
}

inline uint32_t _32_reciprocal32_asm(uint32_t d) noexcept
{
    const auto uh = ~d;
    const auto ul = ~uint32_t{0};
    uint32_t _, v;
    asm("divl %4" : "=d"(_), "=a"(v) : "d"(uh), "a"(ul), "r"(d));
    return v;
}


inline uint32_t hi(uint64_t x) noexcept
{
    return static_cast<uint32_t>(x >> 32);
}

inline uint32_t lo(uint64_t x) noexcept
{
    return static_cast<uint32_t>(x);
}

inline uint64_t uint64(uint32_t hi, uint32_t lo) noexcept
{
    return (uint64_t{hi} << 32) | lo;
}

inline uint32_t _32_reciprocal_3by2(uint64_t d) noexcept
{
    auto v = _32_reciprocal32_asm(hi(d));
    auto p = hi(d) * v;
    p += lo(d);
    if (p < lo(d))
    {
        --v;
        if (p >= hi(d))
        {
            --v;
            p -= hi(d);
        }
        p -= hi(d);
    }

    const auto t = uint64_t{v} * lo(d);

    p += hi(t);
    if (p < hi(t))
    {
        --v;
        if (uint64(p, lo(t)) >= d)
            --v;
    }
    return v;
}

struct _32_res
{
    uint32_t u;
    uint64_t r;
};

inline _32_res _32_udivrem_3by2(uint32_t u2, uint32_t u1, uint32_t u0, uint64_t d, uint32_t v) noexcept
{
    auto q = uint64_t{v} * u2;
    q += uint64(u2, u1);
    auto qh = hi(q);

    auto r1 = u1 - qh * hi(d);

    auto t = uint64_t{lo(d)} * qh;

    auto r = uint64(r1, u0) - t - d;
    r1 = hi(r);

    ++qh;

    if (r1 >= lo(q))
    {
        --qh;
        r += d;
    }

    if (r >= d)
    {
        ++qh;
        r -= d;
    }

    return {qh, r};
}

inline void _32_udivrem_by2(uint32_t u[], uint64_t d) noexcept
{
    const auto reciprocal = _32_reciprocal_3by2(d);

    auto x = _32_udivrem_3by2(u[3], u[2], u[1], d, reciprocal);
    u[1] = x.u;

    auto y = _32_udivrem_3by2(hi(x.r), lo(x.r), u[0], d, reciprocal);
    u[0] = y.u;
}


inline uint64_t reciprocal_2by1_notable(uint64_t d) noexcept
{
    const auto nd = ~d;
    uint32_t u[4] = {
        ~uint32_t{0}, ~uint32_t{0}, static_cast<uint32_t>(nd), static_cast<uint32_t>(nd >> 32)};

    _32_udivrem_by2(u, d);
    return uint64(u[1], u[0]);
}

}  // namespace experimental
}  // namespace intx
