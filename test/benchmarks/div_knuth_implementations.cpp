// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

using namespace intx;

std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_llvm2(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept
{
    constexpr size_t m = 16;
    std::array<uint32_t, 17> un;
    std::array<uint32_t, 16> vn;
    unsigned shift = intx::clz(v[n - 1]);
    uint32_t v_carry = 0;
    uint32_t u_carry = 0;
    if (shift)
    {
        for (size_t i = 0; i < m; ++i)
        {
            uint32_t u_tmp = u[i] >> (32 - shift);
            un[i] = (u[i] << shift) | u_carry;
            u_carry = u_tmp;
        }
        for (size_t i = 0; i < n; ++i)
        {
            uint32_t v_tmp = v[i] >> (32 - shift);
            vn[i] = (v[i] << shift) | v_carry;
            v_carry = v_tmp;
        }
    }
    else
    {
        for (size_t i = 0; i < m; ++i)
            un[i] = u[i];
        for (size_t i = 0; i < n; ++i)
            vn[i] = v[i];
    }
    un[m] = u_carry;
    return {un, vn};
}

std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_llvm3(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept
{
    constexpr size_t m = 16;
    std::array<uint32_t, 17> un;
    std::array<uint32_t, 16> vn;
    unsigned shift = intx::clz(v[n - 1]);
    uint32_t v_carry = 0;
    uint32_t u_carry = 0;
//    if (shift)
    {
        for (size_t i = 0; i < m; ++i)
        {
            uint32_t u_tmp = shift != 0 ? u[i] >> (32 - shift) : 0;
            un[i] = (u[i] << shift) | u_carry;
            u_carry = u_tmp;
        }
        for (size_t i = 0; i < n; ++i)
        {
            uint32_t v_tmp = shift != 0 ? v[i] >> (32 - shift) : 0;
            vn[i] = (v[i] << shift) | v_carry;
            v_carry = v_tmp;
        }
    }
//    else
//    {
//        for (size_t i = 0; i < m; ++i)
//            un[i] = u[i];
//        for (size_t i = 0; i < n; ++i)
//            vn[i] = v[i];
//    }
    un[m] = u_carry;
    return {un, vn};
}

std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_hd2(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept
{
    constexpr size_t m = 16;
    std::array<uint32_t, 17> un;
    std::array<uint32_t, 16> vn;
    unsigned shift = intx::clz(v[n - 1]);
    // shift == 0, we would get shift by 32 => UB. Consider using uint64.
    for (size_t i = n - 1; i > 0; i--)
        vn[i] = shift != 0 ? (v[i] << shift) | (v[i - 1] >> (32 - shift)) : v[i];
    vn[0] = v[0] << shift;

    un[m] = shift != 0 ? u[m - 1] >> (32 - shift) : 0;
    for (size_t i = m - 1; i > 0; i--)
        un[i] = shift != 0 ? (u[i] << shift) | (u[i - 1] >> (32 - shift)) : u[i];
    un[0] = u[0] << shift;
    return {un, vn};
}

std::pair<std::array<uint32_t, 17>, std::array<uint32_t, 16>> udivrem_knuth_normalize_32_hd3(
    const uint32_t u[], const uint32_t v[], size_t n) noexcept
{
    constexpr size_t m = 16;
    std::array<uint32_t, 17> un;
    std::array<uint32_t, 16> vn;
    unsigned shift = intx::clz(v[n - 1]);
    // shift == 0, we would get shift by 32 => UB. Consider using uint64.
    for (size_t i = n - 1; i > 0; i--)
    {
        vn[i] =
            static_cast<uint32_t>((uint64_t(v[i]) << shift) | (uint64_t(v[i - 1]) >> (32 - shift)));
    }
    vn[0] = v[0] << shift;

    un[m] = static_cast<uint32_t>(uint64_t(u[m - 1]) >> (32 - shift));
    for (size_t i = m - 1; i > 0; i--)
        un[i] = static_cast<uint32_t>((uint64_t(u[i]) << shift) | (uint64_t(u[i - 1]) >> (32 - shift)));
    un[0] = u[0] << shift;
    return {un, vn};
}
