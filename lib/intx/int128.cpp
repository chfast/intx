// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div.hpp"
#include <intx/int128.hpp>

namespace intx
{
div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        auto lsh = clz(y.lo);

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

        auto v = reciprocal(yn);

        // OPT: If xn_ex is 0, the result q can be only 0 or 1.
        auto res = udivrem_2by1({xn_ex, xn_hi}, yn, v);
        auto q1 = res.quot;

        res = udivrem_2by1({res.rem, xn_lo}, yn, v);
        auto q0 = res.quot;

        auto q = uint128{q1, q0};
        return {q, res.rem >> lsh};
    }

    if (y.hi > x.hi)
        return {0, x};

    auto lsh = clz(y.hi);

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

    auto v = reciprocal_3by2({yn_hi, yn_lo});
    auto res = udivrem_3by2(xn_ex, xn_hi, xn_lo, {yn_hi, yn_lo}, v);

    return {res.quot, res.rem >> lsh};
}
}  // namespace intx
