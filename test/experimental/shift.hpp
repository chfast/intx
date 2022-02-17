// intx: extended precision integer library.
// Copyright 2022 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

namespace intx::experimental
{
inline constexpr uint64_t shld(uint64_t x1, uint64_t x2, uint64_t c)
{
    if (c == 0)
        return x2;
    return (x2 << c) | (x1 >> (64 - c));
}

template <unsigned N>
[[gnu::noinline]] inline constexpr uint<N> shl_c(const uint<N>& x, const uint64_t& shift) noexcept
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
        z[i] = shld(r[i - 1], r[i], sb);

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

template <unsigned N>
[[gnu::noinline]] inline constexpr uint<N> shl_e(const uint<N>& x, const uint64_t& shift) noexcept
{
    uint<N> r;

    const auto w = shift / 64;

    size_t j = 0;
    for (size_t i = w; i < uint<N>::num_words; ++i, ++j)
        r[i] = x[j];

    const auto sb = shift % uint<N>::word_num_bits;
    if (sb == 0)
        return r;

    uint<N> z;
    z[0] = r[0] << sb;
    for (unsigned i = 1; i < uint<N>::num_words; ++i)
        z[i] = shld(r[i - 1], r[i], sb);

    return z;
}

[[gnu::noinline]] inline constexpr uint256 shl_e(const uint256& x, const uint64_t& shift) noexcept
{
    const auto w = shift / 64;
    const auto s = shift % 64;

    switch (w)
    {
    case 0:
    {
        uint256 r;
        r[0] = x[0] << s;
        r[1] = shld(x[0], x[1], s);
        r[2] = shld(x[1], x[2], s);
        r[3] = shld(x[2], x[3], s);
        return r;
    }
    case 1:
    {
        uint256 r;
        r[1] = x[0] << s;
        r[2] = shld(x[0], x[1], s);
        r[3] = shld(x[1], x[2], s);
        return r;
    }
    case 2:
    {
        uint256 r;
        r[2] = x[0] << s;
        r[3] = shld(x[0], x[1], s);
        return r;
    }
    case 3:
    {
        uint256 r;
        r[3] = x[0] << s;
        return r;
    }
    default:
        return {};
    }
}

template <unsigned N>
inline constexpr uint<N> shl_e(const uint<N>& x, const uint<N>& shift) noexcept
{
    uint64_t high_words_fold = 0;
    for (size_t i = 1; i < uint<N>::num_words; ++i)
        high_words_fold |= shift[i];

    if (INTX_UNLIKELY(high_words_fold != 0))
        return 0;

    return shl_e(x, shift[0]);
}


template <unsigned N>
[[gnu::noinline]] inline constexpr uint<N> shl_w(const uint<N>& x, const uint64_t& shift) noexcept
{
    const auto w = shift / 64;
    const auto s = shift % 64;

    uint<N> r;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        r[i] = i >= w ? x[i - w] : 0;

    if (s == 0)
        return r;

    uint<N> z;
    z[0] = r[0] << s;
    for (unsigned i = 1; i < uint<N>::num_words; ++i)
        z[i] = shld(r[i - 1], r[i], s);

    return z;
}

template <unsigned N>
inline constexpr uint<N> shl_w(const uint<N>& x, const uint<N>& shift) noexcept
{
    uint64_t high_words_fold = 0;
    for (size_t i = 1; i < uint<N>::num_words; ++i)
        high_words_fold |= shift[i];

    if (INTX_UNLIKELY(high_words_fold != 0))
        return 0;

    return shl_w(x, shift[0]);
}


inline uint64_t shrd(uint64_t x1, uint64_t x2, uint64_t c)
{
    return (x2 >> c) | (x1 << (64 - c));
}

template <unsigned N>
uint<N> shr_c(const uint<N>& x, const uint64_t& shift) noexcept
{
    uint<2 * N> extended;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        extended[i] = x[i];

    const auto sw =
        shift >= uint<N>::num_bits ? uint<N>::num_words : shift / uint<N>::word_num_bits;

    uint<N> r;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        r[i] = extended[size_t(sw + i)];

    const auto sb = shift % uint<N>::word_num_bits;
    if (sb == 0)
        return r;

    constexpr auto nw = uint<N>::num_words;

    uint<N> z;
    z[nw - 1] = r[nw - 1] >> sb;

    for (unsigned i = 0; i < nw - 1; ++i)
        z[nw - i - 2] = shrd(r[nw - i - 1], r[nw - i - 2], sb);

    return z;
}

template <unsigned N>
inline constexpr uint<N> shr_c(const uint<N>& x, const uint<N>& shift) noexcept
{
    uint64_t high_words_fold = 0;
    for (size_t i = 1; i < uint<N>::num_words; ++i)
        high_words_fold |= shift[i];

    if (INTX_UNLIKELY(high_words_fold != 0))
        return 0;

    return shr_c(x, shift[0]);
}

}  // namespace intx::experimental
