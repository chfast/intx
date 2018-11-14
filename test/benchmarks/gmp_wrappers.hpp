// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <gmp.h>
#include <intx/intx.hpp>

using namespace intx;

std::tuple<uint256, uint64_t> udivrem_1_64_gmp(const uint256& u, uint64_t v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint256 q;
    uint64_t r;
    auto p_q = (mp_ptr)&q;
    auto p_u = (mp_srcptr)&u;
    mpn_tdiv_qr(p_q, &r, 0, p_u, gmp_limbs, &v, 1);
    return std::make_tuple(q, r);
};

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

std::tuple<uint512, uint512> udivrem_gmp(const uint512& u, const uint512& v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint512 q;
    uint512 r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_u = (mp_srcptr)&u;
    auto p_v = (mp_srcptr)&v;
    mpn_tdiv_qr(p_q, p_r, 0, p_u, gmp_limbs, p_v, gmp_limbs);
    return std::make_tuple(q, r);
};

std::tuple<uint512, uint256> udivrem_gmp(const uint512& u, const uint256& v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint512 q;
    uint256 r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_u = (mp_srcptr)&u;
    auto p_v = (mp_srcptr)&v;
    mpn_tdiv_qr(p_q, p_r, 0, p_u, gmp_limbs, p_v, gmp_limbs / 2);
    return std::make_tuple(q, r);
};

std::tuple<uint512, uint128> udivrem_gmp(const uint512& u, const uint128& v) noexcept
{
    static_assert(sizeof(mp_limb_t) == sizeof(uint64_t), "Wrong GMP mp_limb_t type");
    constexpr size_t gmp_limbs = sizeof(u) / sizeof(mp_limb_t);

    uint512 q;
    uint128 r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_u = (mp_srcptr)&u;
    auto p_v = (mp_srcptr)&v;
    mpn_tdiv_qr(p_q, p_r, 0, p_u, gmp_limbs, p_v, gmp_limbs / 4);
    return std::make_tuple(q, r);
};
