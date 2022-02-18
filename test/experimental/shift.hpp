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
[[gnu::noinline]] inline constexpr uint<N> shl_c(const uint<N>& x, uint64_t shift) noexcept
{
    uint<2 * N> extended;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        extended[i + uint<N>::num_words] = x[i];

    const auto s = shift / uint<N>::word_num_bits;
    const auto sw = s < uint<N>::num_words ? s : uint<N>::num_words;

    uint<N> r;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
        r[i] = extended[size_t(uint<N>::num_words - sw + i)];

    const auto sb = shift % uint<N>::word_num_bits;
    const auto m = uint64_t{1} << sb;

    uint<N> z;
    uint64_t k = 0;
    for (unsigned i = 0; i < uint<N>::num_words; ++i)
    {
        const auto p = umul(r[i], m);
        z[i] = p[0] + k;
        k = p[1];
    }

    return z;
}

[[gnu::noinline]] inline uint256 shl_bits_1(const uint256& x, uint64_t sb) noexcept
{
    if (sb == 0)
        __builtin_unreachable();
    uint256 z;
    z[0] = x[0] << sb;
    for (unsigned i = 1; i < uint256::num_words; ++i)
        z[i] = shld(x[i - 1], x[i], sb);
    return z;
}

[[gnu::noinline]] inline uint256 shl_bits_2(const uint256& x, uint64_t sb) noexcept
{
    if (sb == 0)
        __builtin_unreachable();

    const auto t = 64 - sb;

    uint256 r;
    uint64_t carry = 0;
    for (size_t i = 0; i < uint256::num_words; ++i)
    {
        auto a = x[i];
        auto b = a << sb;
        auto c = b | carry;
        carry = a >> t;
        r[i] = c;
    }
    return r;
}

[[gnu::noinline]] inline uint256 shl_bits_3(const uint256& x, uint64_t sb) noexcept
{
    if (sb == 0)
        __builtin_unreachable();

    static constexpr size_t num_words = 4;
    size_t skip = 0;
    uint256 r;
    uint64_t carry = 0;
    for (size_t i = 0; i < (num_words - skip); ++i)
    {
        r[num_words - 1 - i - skip] = (x[num_words - 1 - i] >> sb) | carry;
        carry = (x[num_words - 1 - i] << (64 - sb - 1)) << 1;
    }
    return r;
}

[[gnu::noinline]] inline uint256 shl_bits_4(const uint256& x, uint64_t sb) noexcept
{
    if (sb == 0)
        __builtin_unreachable();

    static constexpr size_t num_words = 4;
    size_t skip = 0;
    uint256 r;
    uint64_t carry = 0;
    for (size_t i = 0; i < (num_words - skip); ++i)
    {
        r[num_words - 1 - i - skip] = (x[num_words - 1 - i] >> sb) | carry;
        carry = (x[num_words - 1 - i] << (64 - sb));
    }
    return r;
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
[[gnu::noinline]] inline constexpr uint<N> shl_e(const uint<N>& x, uint64_t shift) noexcept
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

[[gnu::noinline]] inline constexpr uint256 shl_e(const uint256& x, uint64_t shift) noexcept
{
    const auto w = shift / 64;
    const auto s = shift % 64;

    uint256 r;
    switch (w)
    {
    case 0:
    {
        r = x;
        break;
    }
    case 1:
    {
        r[1] = x[0];
        r[2] = x[1];
        r[3] = x[2];
        break;
    }
    case 2:
    {
        r[2] = x[0];
        r[3] = x[1];
        break;
    }
    case 3:
    {
        r[3] = x[0];
        break;
    }
    default:
        break;
    }

    if (s == 0)
        return r;

    switch (w)
    {
    case 0:
    {
        r[3] = shld(r[2], r[3], s);
        r[2] = shld(r[1], r[2], s);
        r[1] = shld(r[0], r[1], s);
        r[0] = r[0] << s;
        break;
    }
    case 1:
    {
        r[3] = shld(r[2], r[3], s);
        r[2] = shld(r[1], r[2], s);
        r[1] = r[1] << s;
        break;
    }
    case 2:
    {
        r[3] = shld(r[2], r[3], s);
        r[2] = r[2] << s;
        break;
    }
    case 3:
    {
        r[3] = r[3] << s;
        break;
    }
    default:
        break;
    }

    return r;
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
[[gnu::noinline]] inline constexpr uint<N> shl_w(const uint<N>& x, uint64_t shift) noexcept
{
    const auto w = shift / 64;
    const auto s = shift % 64;
    const auto t = s == 0 ? 0 : 64 - s;
    const auto m = s == 0 ? 0 : ~uint64_t{0};

    uint<N> r;
    uint64_t carry = 0;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
    {
        auto a = i >= w ? x[i - w] : 0;
        auto b = a << s;
        auto c = b | carry;
        carry = a >> t;
        carry &= m;
        r[i] = c;
    }
    return r;
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
