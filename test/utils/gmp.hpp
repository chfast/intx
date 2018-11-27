// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <gmp.h>
#include <intx/intx.hpp>

namespace intx
{
static constexpr size_t gmp_limbs = sizeof(uint256) / sizeof(mp_limb_t);

uint256 gmp_mul(uint256 x, uint256 y) noexcept
{
    uint256 p[2];
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, gmp_limbs);
    return p[0];
}

uint512 gmp_mul_full(uint256 x, uint256 y) noexcept
{
    uint512 p;
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, gmp_limbs);
    return p;
}

uint512 gmp_mul(uint512 x, uint512 y) noexcept
{
    uint512 p[2];
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, gmp_limbs * 2);
    return p[0];
}

template<typename Int>
std::tuple<Int, Int> gmp_udiv_qr(Int x, Int y) noexcept
{
    // Skip dividend's leading zero limbs.
    constexpr size_t gmp_limbs = sizeof(Int) / sizeof(mp_limb_t);
    const size_t y_limbs = count_significant_words<mp_limb_t>(y);

    Int q, r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_tdiv_qr(p_q, p_r, 0, p_x, gmp_limbs, p_y, y_limbs);
    return std::make_tuple(q, r);
};

namespace gmp
{
template<typename Int>
Int add(const Int& x, const Int& y) noexcept
{
    constexpr size_t gmp_limbs = sizeof(Int) / sizeof(mp_limb_t);

    Int s;
    auto p_s = (mp_ptr)&s;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_add(p_s, p_x, gmp_limbs, p_y, gmp_limbs);
    return s;
};
}
}
