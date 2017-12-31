// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <gmp.h>
#include <intx/intx.hpp>

namespace intx
{
static std::tuple<uint256, uint256> gmp_udiv_qr(uint256 x, uint256 y)
{
    // Skip dividend's leading zero limbs.
    static constexpr size_t limbs = sizeof(uint256) / sizeof(mp_limb_t);
    const size_t y_limbs = limbs - (clz(y) / (sizeof(mp_limb_t) * 8));

    uint256 q, r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_tdiv_qr(p_q, p_r, 0, p_x, limbs, p_y, y_limbs);
    return {q, r};
};
}
