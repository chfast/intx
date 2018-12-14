// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

/// @file
/// Wrappers for GMP functions.

#pragma once

#include <gmp.h>
#include <intx/intx.hpp>

namespace intx
{
namespace gmp
{
static constexpr size_t uint256_limbs = sizeof(uint256) / sizeof(mp_limb_t);

inline uint256 mul(const uint256& x, const uint256& y) noexcept
{
    uint256 p[2];
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, uint256_limbs);
    return p[0];
}

inline uint512 mul_full(const uint256& x, const uint256& y) noexcept
{
    uint512 p;
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, uint256_limbs);
    return p;
}

inline uint512 mul(const uint512& x, const uint512& y) noexcept
{
    uint512 p[2];
    auto p_p = (mp_ptr)&p;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_mul_n(p_p, p_x, p_y, uint256_limbs * 2);
    return p[0];
}

template <typename Int>
inline std::tuple<Int, Int> udivrem(const Int& x, const Int& y) noexcept
{
    // Skip dividend's leading zero limbs.
    constexpr size_t x_limbs = sizeof(Int) / sizeof(mp_limb_t);
    const size_t y_limbs = count_significant_words<mp_limb_t>(y);

    Int q, r;
    auto p_q = (mp_ptr)&q;
    auto p_r = (mp_ptr)&r;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_tdiv_qr(p_q, p_r, 0, p_x, x_limbs, p_y, y_limbs);
    return std::make_tuple(q, r);
};

template <typename Int>
inline std::tuple<Int, Int> sdivrem(const Int& x, const Int& y) noexcept
{
    const auto sign_bit_mask = Int(1) << (sizeof(Int) * 8 - 1);
    auto x_is_neg = (x & sign_bit_mask) != 0;
    auto y_is_neg = (y & sign_bit_mask) != 0;

    auto x_abs = x_is_neg ? -x : x;
    auto y_abs = y_is_neg ? -y : y;

    mpz_t x_gmp;
    mpz_init_set_str(x_gmp, to_string(x_abs).c_str(), 10);
    if (x_is_neg)
        mpz_neg(x_gmp, x_gmp);

    mpz_t y_gmp;
    mpz_init_set_str(y_gmp, to_string(y_abs).c_str(), 10);
    if (y_is_neg)
        mpz_neg(y_gmp, y_gmp);

    mpz_t q_gmp;
    mpz_init(q_gmp);
    mpz_t r_gmp;
    mpz_init(r_gmp);

    mpz_tdiv_qr(q_gmp, r_gmp, x_gmp, y_gmp);

    char buf[200];

    mpz_get_str(buf, 10, q_gmp);
    auto q_is_neg = buf[0] == '-';
    auto q = from_string<Int>(&buf[q_is_neg]);
    if (q_is_neg)
        q = -q;

    mpz_get_str(buf, 10, r_gmp);
    auto r_is_neg = buf[0] == '-';
    auto r = from_string<Int>(&buf[r_is_neg]);
    if (r_is_neg)
        r = -r;

    mpz_clears(x_gmp, y_gmp, q_gmp, r_gmp, NULL);

    return {q, r};
};

template <typename Int>
inline Int add(const Int& x, const Int& y) noexcept
{
    constexpr size_t gmp_limbs = sizeof(Int) / sizeof(mp_limb_t);

    Int s;
    auto p_s = (mp_ptr)&s;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_add_n(p_s, p_x, p_y, gmp_limbs);
    return s;
}

template <typename Int>
inline Int sub(const Int& x, const Int& y) noexcept
{
    constexpr size_t gmp_limbs = sizeof(Int) / sizeof(mp_limb_t);

    Int s;
    auto p_s = (mp_ptr)&s;
    auto p_x = (mp_srcptr)&x;
    auto p_y = (mp_srcptr)&y;
    mpn_sub_n(p_s, p_x, p_y, gmp_limbs);
    return s;
}
}  // namespace gmp
}  // namespace intx
