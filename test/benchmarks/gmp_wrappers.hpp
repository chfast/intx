// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <gmp.h>
#include <intx/int128.hpp>
#include <tuple>

using namespace intx;

std::tuple<uint128, uint128> udivrem_gmp(const uint128& u, const uint128& v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint128 q, r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_u = (mp_srcptr)&u;
    auto p_v = (mp_srcptr)&v;
    mpn_tdiv_qr(p_q, p_r, 0, p_u, gmp_limbs, p_v, gmp_limbs);
    return std::make_tuple(q, r);
}
