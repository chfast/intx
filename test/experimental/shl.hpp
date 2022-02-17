// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

namespace intx
{
namespace experimental
{
template <unsigned N>
inline constexpr auto shld(
    typename uint<N>::word_type x1, typename uint<N>::word_type x2, uint64_t c)
{
    return (x2 << c) | (x1 >> (uint<N>::word_num_bits - c));
}

template <unsigned N>
inline constexpr uint<N> shl_c(const uint<N>& x, const uint64_t& shift) noexcept
{
    uint<2 * N> extended;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        extended[i + uint<N>::num_words] = x[i];

    const auto sw =
        shift >= uint<N>::num_bits ? uint<N>::num_words : shift / uint<N>::word_num_bits;

    uint<N> r;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        r[i] = extended[size_t(uint<N>::num_words - sw + i)];

    const auto sb = shift % uint<N>::word_num_bits;
    if (sb == 0)
        return r;

    uint<N> z;

    z[0] = r[0] << sb;
    for (unsigned i = 1; i < uint<N>::num_words; ++i)
        z[i] = shld<N>(r[i - 1], r[i], sb);

    return z;
}

template <unsigned N>
inline constexpr uint<N> shl_c(const uint<N>& x, const uint<N>& shift) noexcept
{
    uint64_t high_words_fold = 0;
    for (size_t i = 1; i < uint<N>::num_words; ++i)
        high_words_fold |= shift[i];

    if (INTX_UNLIKELY(high_words_fold != 0))
        return 0;

    return shl_c(x, shift[0]);
}

}  // namespace experimental
}  // namespace intx