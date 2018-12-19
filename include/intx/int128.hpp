// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <intx/builtins.h>
#include <intx/mul_full.h>
#include <cstdint>
#include <type_traits>

namespace intx
{
struct uint128
{
    uint64_t lo = 0;
    uint64_t hi = 0;

    constexpr uint128() noexcept = default;

    template <typename T>
    constexpr uint128(typename std::enable_if<std::is_unsigned<T>::value>::type x) noexcept : lo{x}
    {}

    template <typename T>
    constexpr explicit uint128(typename std::enable_if<std::is_signed<T>::value>::type x) noexcept
      : lo{static_cast<uint64_t>(x)}
    {}

    constexpr uint128(uint64_t hi, uint64_t lo) noexcept : lo{lo}, hi{hi} {}

#ifdef __SIZEOF_INT128__
    constexpr uint128(unsigned __int128 x) noexcept : lo{uint64_t(x)}, hi{uint64_t(x >> 64)} {}
#endif
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


constexpr uint128 operator<<(const uint128& x, unsigned shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 right shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{(x.hi << shift) | ((x.lo >> 1) >> (63 - shift)), x.lo << shift} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{x.lo << (shift - 64), 0} : 0;
}

constexpr uint128 operator>>(const uint128& x, unsigned shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 left shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{x.hi >> shift, (x.lo >> shift) | ((x.hi << 1) << (63 - shift))} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{0, x.hi >> (shift - 64)} : 0;
}

inline uint128& operator<<=(uint128& x, unsigned shift) noexcept
{
    return x = x << shift;
}

inline uint128& operator>>=(uint128& x, unsigned shift) noexcept
{
    return x = x >> shift;
}


uint128 operator/(const uint128& x, const uint128& y) noexcept;
uint128 operator%(const uint128& x, const uint128& y) noexcept;


inline int clz(const uint128& x)
{
    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    return x.hi == 0 ? builtins::clz(x.lo) | 64 : builtins::clz(x.hi);
}

}  // namespace intx
