// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <gmp.h>
#include <intx/intx.hpp>

using namespace intx;

std::tuple<uint512, uint64_t> udivrem_1_64_gmp(const uint512& u, uint64_t v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint512 q;
    uint64_t r;
    auto p_q = (mp_ptr)&q;
    auto p_u = (mp_srcptr)&u;
    mpn_tdiv_qr(p_q, &r, 0, p_u, gmp_limbs, &v, 1);
    return std::make_tuple(q, r);
};
