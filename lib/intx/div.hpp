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
inline normalized_div_args<IntT::num_bits> normalize(
    const IntT& numerator, const IntT& denominator) noexcept
{
    // FIXME: Make the implementation type independent
    static constexpr auto num_words = IntT::num_words;

    normalized_div_args<IntT::num_bits> na;

    // FIXME: Not needed, but checked in tests
    na.numerator_ex = 0;

    std::tie(na.num_divisor_words, na.shift) =
        normalize_divisor(as_words(na.divisor), as_words(denominator), num_words);

    na.num_numerator_words =
        normalize_numerator(as_words(na.numerator), as_words(numerator), num_words, na.shift);

    // Skip the highest word of numerator if not significant.
    if (as_words(na.numerator)[na.num_numerator_words] != 0 ||
        as_words(na.numerator)[na.num_numerator_words - 1] >=
            as_words(na.divisor)[na.num_divisor_words - 1])
        ++na.num_numerator_words;

    return na;
}

}  // namespace intx
