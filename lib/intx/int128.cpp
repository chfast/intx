// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "experiments.hpp"
#include <intx/int128.hpp>

namespace intx
{
namespace experiments
{
div_result<uint64_t> udivrem_2by1(uint64_t u1, uint64_t u0, uint64_t d, uint64_t v) noexcept;
div_result<uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint64_t d1, uint64_t d0) noexcept;
}  // namespace experiments

namespace
{
inline div_result<uint64_t> udivrem_long(uint128 u, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(u.hi), "a"(u.lo), "g"(v));
    return {q, r};
}

div_result<uint128> udivrem_old(uint128 x, uint128 y) noexcept
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
    return udivrem_old(x, y).quot;
}

uint128 operator%(uint128 x, uint128 y) noexcept
{
    return udivrem_old(x, y).rem;
}

div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
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
        auto res = udivrem_long({r, x.lo}, y.lo);
        return {{hi, res.quot}, res.rem};
    }

    if (y.hi > x.hi)
        return {0, x};

    auto lsh = __builtin_clzl(y.hi);

    if (lsh == 0)
    {
        bool q = (y.hi < x.hi) | (y.lo <= x.lo);
        return {q, x - (q ? y : 0)};
    }

    auto rsh = 64 - lsh;

    auto yn_lo = y.lo << lsh;
    auto yn_hi = (y.lo >> rsh) | (y.hi << lsh);
    auto xn_ex = x.hi >> rsh;
    auto xn_hi = (x.lo >> rsh) | (x.hi << lsh);
    auto res = udivrem_long({xn_ex, xn_hi}, yn_hi);
    auto m = mul_full_64(res.quot, yn_lo);
    if (res.rem <= m.hi)
        --res.quot;
    return {res.quot, x - y * res.quot};
}

div_result<uint128> udivrem_by_reciprocal(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        auto lsh = __builtin_clzl(y.lo);

        uint64_t xn_ex, xn_hi, xn_lo, yn;

        if (lsh != 0)
        {
            auto rsh = 64 - lsh;
            xn_ex = x.hi >> rsh;
            xn_hi = (x.lo >> rsh) | (x.hi << lsh);
            xn_lo = x.lo << lsh;
            yn = y.lo << lsh;
        }
        else
        {
            xn_ex = 0;
            xn_hi = x.hi;
            xn_lo = x.lo;
            yn = y.lo;
        }

        auto v = experiments::reciprocal(yn);

        // OPT: If xn_ex is 0, the result q can be only 0 or 1.
        auto res = experiments::udivrem_2by1(xn_ex, xn_hi, yn, v);
        auto q1 = res.quot;

        res = experiments::udivrem_2by1(res.rem, xn_lo, yn, v);
        auto q0 = res.quot;

        auto q = uint128{q1, q0};
        return {q, res.rem >> lsh};
    }

    if (y.hi > x.hi)
        return {0, x};

    auto lsh = __builtin_clzl(y.hi);

    if (lsh == 0)
    {
        bool q = (y.hi < x.hi) | (y.lo <= x.lo);
        return {q, x - (q ? y : 0)};
    }

    auto rsh = 64 - lsh;

    auto yn_lo = y.lo << lsh;
    auto yn_hi = (y.lo >> rsh) | (y.hi << lsh);
    auto xn_ex = x.hi >> rsh;
    auto xn_hi = (x.lo >> rsh) | (x.hi << lsh);
    auto xn_lo = x.lo << lsh;

    auto res = experiments::udivrem_3by2(xn_ex, xn_hi, xn_lo, yn_hi, yn_lo);

    return {res.quot, res.rem >> lsh};
}

}  // namespace intx
