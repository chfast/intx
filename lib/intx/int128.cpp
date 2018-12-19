// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

namespace intx
{
namespace
{
template <typename T>
struct div_result
{
    T quot;
    T rem;
};

inline div_result<uint64_t> udivrem_long(uint128 u, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(u.hi), "a"(u.lo), "g"(v));
    return {q, r};
}

div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        auto res = udivrem_long({x.hi % y.lo, x.lo}, y.lo);
        return {{x.hi / y.lo, res.quot}, res.rem};
    }

    int shift = builtins::clz(y.hi);
    uint128 vn = y << shift;
    uint128 un = x << shift;
    uint64_t unx = shift ? x.hi >> (64 - shift) : 0;

    auto res = udivrem_long({unx, un.hi}, vn.hi);
    if (uint128(res.quot) * vn.lo > uint128{res.rem, un.lo})
        --res.quot;

    return {res.quot, x - (y * res.quot)};
}

}  // namespace

uint128 operator/(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).quot;
}

uint128 operator%(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).rem;
}

uint128 udiv(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        uint64_t hi = 0;
        auto r = x.hi;
        if (y.lo <= x.hi)
        {
            hi = x.hi / y.lo;
            r = x.hi % y.lo;
        }
        auto lo = udivrem_long({r, x.lo}, y.lo).quot;
        return {hi, lo};
    }

    if (y.hi > x.hi)
        return 0;

    auto lsh = __builtin_clzl(y.hi);

    if (lsh == 0)
        return (y.hi < x.hi) | (y.lo <= x.lo);

    auto rsh = 64 - lsh;

    auto yn_lo = y.lo << lsh;
    auto yn_hi = (y.lo >> rsh) | (y.hi << lsh);
    auto xn_ex = x.hi >> rsh;
    auto xn_hi = (x.lo >> rsh) | (x.hi << lsh);
    auto res = udivrem_long({xn_ex, xn_hi}, yn_hi);
    uint64_t m_hi;
    mul_full_64(res.quot, yn_lo, &m_hi);
    if (res.rem <= m_hi)
        --res.quot;
    return res.quot;
}

}  // namespace intx
