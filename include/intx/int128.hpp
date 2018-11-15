// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <intx/builtins.h>
#include <intx/mul_full.h>
#include <cstdint>

namespace intx
{
struct uint128
{
    uint64_t lo = 0;
    uint64_t hi = 0;

    constexpr uint128() noexcept = default;

    constexpr uint128(uint64_t x) noexcept : lo{x} {}

    constexpr uint128(uint64_t hi, uint64_t lo) noexcept : lo{lo}, hi{hi} {}
};


constexpr bool operator==(const uint128& x, const uint128& y) noexcept
{
    // Bitwise & used to avoid branching.
    return (x.lo == y.lo) & (x.hi == y.hi);
}

constexpr bool operator!=(const uint128& x, const uint128& y) noexcept
{
    return !(x == y);
}

constexpr bool operator<(const uint128& x, const uint128& y) noexcept
{
    // Bitwise operators are used to avoid branching.
    return (x.hi < y.hi) | ((x.hi == y.hi) & (x.lo < y.lo));
}

constexpr bool operator<=(const uint128& x, const uint128& y) noexcept
{
    // Bitwise | used to avoid branching.
    return (x < y) | (x == y);
}

constexpr bool operator>(const uint128& x, const uint128& y) noexcept
{
    return !(x <= y);
}

constexpr bool operator>=(const uint128& x, const uint128& y) noexcept
{
    return !(x < y);
}


constexpr uint128 operator|(const uint128& x, const uint128& y) noexcept
{
    return {x.hi | y.hi, x.lo | y.lo};
}

constexpr uint128 operator&(const uint128& x, const uint128& y) noexcept
{
    return {x.hi & y.hi, x.lo & y.lo};
}

constexpr uint128 operator^(const uint128& x, const uint128& y) noexcept
{
    return {x.hi ^ y.hi, x.lo ^ y.lo};
}

constexpr uint128 operator~(const uint128& x) noexcept
{
    return {~x.hi, ~x.lo};
}


constexpr uint128 operator+(const uint128& x, const uint128& y) noexcept
{
    return {x.hi + y.hi + (x.lo > (x.lo + y.lo)), x.lo + y.lo};
}

constexpr uint128 operator-(const uint128& x) noexcept
{
    return ~x + 1;
}

constexpr uint128 operator-(const uint128& x, const uint128& y) noexcept
{
    return x + -y;
}

inline uint128& operator+=(uint128& x, const uint128& y) noexcept
{
    return x = x + y;
}

inline uint128& operator-=(uint128& x, const uint128& y) noexcept
{
    return x = x - y;
}

inline uint128& operator|=(uint128& x, const uint128& y) noexcept
{
    return x = x | y;
}

inline uint128& operator&=(uint128& x, const uint128& y) noexcept
{
    return x = x & y;
}

inline uint128& operator^=(uint128& x, const uint128& y) noexcept
{
    return x = x ^ y;
}


inline uint128 operator*(const uint128& x, const uint128& y) noexcept
{
    uint128 p;
    p.lo = mul_full_64(x.lo, y.lo, &p.hi);
    p.hi += (x.lo * y.hi) + (x.hi * y.lo);
    return p;
}


inline uint128 operator<<(const uint128& x, unsigned shift) noexcept
{
    if (shift < 64)
    {
        // Find the part moved from lo to hi.
        // For shift == 0 => rshift == 64 is invalid so
        // split it into 2 valid shifts by 1 and (rshift - 1).
        unsigned rshift = 64 - shift;
        auto lo_overflow = (x.lo >> 1) >> (rshift - 1);
        return {(x.hi << shift) | lo_overflow, x.lo << shift};
    }

    // Guarantee "defined" behavior for shifts larger than 128.
    if (shift < 128)
        return {x.lo << (shift - 64), 0};

    return 0;
}

inline uint128 operator>>(const uint128& x, unsigned shift) noexcept
{
    if (shift < 64)
    {
        // Find the part moved from lo to hi.
        // For shift == 0 => lshift == 64 is invalid so
        // split it into 2 valid shifts by 1 and (lshift - 1).
        unsigned lshift = 64 - shift;
        auto hi_overflow = (x.hi << 1) << (lshift - 1);
        return {x.hi >> shift, (x.lo >> shift) | hi_overflow};
    }

    // Guarantee "defined" behavior for shifts larger than 128.
    if (shift < 128)
        return {0, x.hi >> (shift - 64)};

    return 0;
}


inline int clz(const uint128& x)
{
    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    return x.hi == 0 ? builtins::clz(x.lo) | 64 : builtins::clz(x.hi);
}

}  // namespace intx
