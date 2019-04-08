// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/intx.hpp>

namespace intx
{
inline div_result<uint64_t> udivrem_long(uint128 x, uint64_t y) noexcept
{
    auto shift = clz(y);
    auto yn = y << shift;
    auto xn = x << shift;
    auto v = reciprocal_2by1(yn);
    auto res = udivrem_2by1(xn, yn, v);
    return {res.quot, res.rem >> shift};
}

struct normalized_div_args
{
    using word_type = uint64_t;

    std::array<word_type, sizeof(uint512) / sizeof(word_type) + 1> numerator;
    std::array<word_type, sizeof(uint512) / sizeof(word_type)> denominator;
    int num_numerator_words;
    int num_denominator_words;
    int shift;
};

inline normalized_div_args normalize(const uint512& numerator, const uint512& denominator) noexcept
{
    static constexpr auto num_words = int{sizeof(uint512) / sizeof(normalized_div_args::word_type)};

    auto* u = as_words(numerator);
    auto* v = as_words(denominator);

    normalized_div_args na;
    auto* un = &na.numerator[0];
    auto* vn = &na.denominator[0];

    auto& m = na.num_numerator_words;
    for (m = num_words; m > 0 && u[m - 1] == 0; --m)
        ;

    auto& n = na.num_denominator_words;
    for (n = num_words; n > 0 && v[n - 1] == 0; --n)
        ;

    na.shift = clz(v[n - 1]);
    if (na.shift)
    {
        for (int i = num_words - 1; i > 0; --i)
            vn[i] = (v[i] << na.shift) | (v[i - 1] >> (64 - na.shift));
        vn[0] = v[0] << na.shift;

        un[num_words] = u[num_words - 1] >> (64 - na.shift);
        for (int i = num_words - 1; i > 0; --i)
            un[i] = (u[i] << na.shift) | (u[i - 1] >> (64 - na.shift));
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
