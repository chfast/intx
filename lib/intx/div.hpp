// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/intx.hpp>

namespace intx
{
struct normalized_div_args
{
    uint<512> denominator;
    uint<512> numerator;
    uint<512>::word_type numerator_ex;
    int num_denominator_words;
    int num_numerator_words;
    int shift;
};

inline normalized_div_args normalize(const uint512& numerator, const uint512& denominator) noexcept
{
    static constexpr auto num_words = uint512::num_words;

    auto* u = as_words(numerator);
    auto* v = as_words(denominator);

    normalized_div_args na;
    auto* un = as_words(na.numerator);
    auto* vn = as_words(na.denominator);

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
