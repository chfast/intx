// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <intx/builtins.h>
#include <intx/intx.hpp>

namespace intx
{
uint64_t reciprocal(uint64_t d) noexcept;
uint64_t reciprocal_3by2(uint128 d) noexcept;
div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept;
div_result<uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint128 d, uint64_t v) noexcept;

struct normalized_args
{
    std::array<uint32_t, sizeof(uint512) / sizeof(uint32_t) + 1> numerator;
    std::array<uint32_t, sizeof(uint512) / sizeof(uint32_t)> denominator;
    int num_numerator_words;
    int num_denominator_words;
    int shift;
};

inline normalized_args normalize(const uint512& numerator, const uint512& denominator) noexcept
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    auto* u = reinterpret_cast<const uint32_t*>(&numerator);
    auto* v = reinterpret_cast<const uint32_t*>(&denominator);

    normalized_args na;
    auto* un = &na.numerator[0];
    auto* vn = &na.denominator[0];

    auto& m = na.num_numerator_words;
    for (m = num_words; m > 0 && u[m - 1] == 0; --m)
        ;

    auto& n = na.num_denominator_words;
    for (n = num_words; n > 0 && v[n - 1] == 0; --n)
        ;

    na.shift = builtins::clz(v[n - 1]);
    if (na.shift)
    {
        for (int i = num_words - 1; i > 0; --i)
            vn[i] = (v[i] << na.shift) | (v[i - 1] >> (32 - na.shift));
        vn[0] = v[0] << na.shift;

        un[num_words] = u[num_words - 1] >> (32 - na.shift);
        for (int i = num_words - 1; i > 0; --i)
            un[i] = (u[i] << na.shift) | (u[i - 1] >> (32 - na.shift));
        un[0] = u[0] << na.shift;
    }
    else
    {
        un[num_words] = 0;
        std::memcpy(un, u, sizeof(numerator));
        std::memcpy(vn, v, sizeof(denominator));
    }

    return na;
}

}  // namespace intx
