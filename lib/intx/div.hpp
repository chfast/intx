// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <cassert>
#include <intx/intx.hpp>

namespace intx
{
template <unsigned N>
struct normalized_div_args
{
    uint<N> divisor;
    uint<N> numerator;
    typename uint<N>::word_type numerator_ex;
    int num_divisor_words;
    int num_numerator_words;
    unsigned shift;
};

std::tuple<int, unsigned> normalize_divisor(uint64_t* dn, const uint64_t* d, int n) noexcept;

int normalize_numerator(uint64_t* un, const uint64_t* u, int n, unsigned shift) noexcept;

template <typename IntT>
[[gnu::always_inline]] inline normalized_div_args<IntT::num_bits> normalize(
    const IntT& numerator, const IntT& denominator) noexcept
{
    // FIXME: Make the implementation type independent
    static constexpr auto num_words = IntT::num_words;

    auto* u = as_words(numerator);

    normalized_div_args<IntT::num_bits> na;

    std::tie(na.num_divisor_words, na.shift) =
        normalize_divisor(as_words(na.divisor), as_words(denominator), num_words);

    auto* un = as_words(na.numerator);

    auto& m = na.num_numerator_words;
    for (m = num_words; m > 0 && u[m - 1] == 0; --m)
        ;

    if (na.shift)
    {
        un[num_words] = u[num_words - 1] >> (64 - na.shift);
        for (int i = num_words - 1; i > 0; --i)
            un[i] = (u[i] << na.shift) | (u[i - 1] >> (64 - na.shift));
        un[0] = u[0] << na.shift;
    }
    else
    {
        na.numerator_ex = 0;
        na.numerator = numerator;
    }

    {
        uint64_t _un[num_words + 1]{};
        auto n = normalize_numerator(_un, u, num_words, na.shift);
        assert(na.num_numerator_words == n);

        for (int i = 0; i <= n; i++)
        {
            assert(_un[i] == as_words(na.numerator)[i]);
        }
    }

    // Skip the highest word of numerator if not significant.
    if (as_words(na.numerator)[na.num_numerator_words] != 0 ||
        as_words(na.numerator)[na.num_numerator_words - 1] >=
            as_words(na.divisor)[na.num_divisor_words - 1])
        ++na.num_numerator_words;

    return na;
}

}  // namespace intx
