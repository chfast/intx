// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <cstdint>
#include <type_traits>

#ifdef _MSC_VER
#include <intrin.h>
#endif

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

    constexpr explicit operator unsigned __int128() const noexcept
    {
        return (static_cast<unsigned __int128>(hi) << 64) | lo;
    }
#endif

    /// Explicit converting operator for all builtin integral types.
    template <typename Int, typename = typename std::enable_if<std::is_integral<Int>::value>::type>
    constexpr explicit operator Int() const noexcept
    {
        return static_cast<Int>(lo);
    }
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
    return {x.hi - y.hi - (x.lo < (x.lo - y.lo)), x.lo - y.lo};
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

inline uint128 umul_generic(uint64_t x, uint64_t y) noexcept
{
    uint64_t xl = x & 0xffffffff;
    uint64_t xh = x >> 32;
    uint64_t yl = y & 0xffffffff;
    uint64_t yh = y >> 32;

    uint64_t t0 = xl * yl;
    uint64_t t1 = xh * yl;
    uint64_t t2 = xl * yh;
    uint64_t t3 = xh * yh;

    uint64_t u1 = t1 + (t0 >> 32);
    uint64_t u2 = t2 + (u1 & 0xffffffff);

    uint64_t lo = (u2 << 32) | (t0 & 0xffffffff);
    uint64_t hi = t3 + (u2 >> 32) + (u1 >> 32);
    return {hi, lo};
}

/// Full unsigned multiplication 64 x 64 -> 128.
inline uint128 umul(uint64_t x, uint64_t y) noexcept
{
#if defined(__SIZEOF_INT128__)
    auto p = (unsigned __int128){x} * y;
    return {uint64_t(p >> 64), uint64_t(p)};
#elif defined(_MSC_VER)
    uint64_t hi;
    auto lo = _mul128(x, y, &hi);
    return {hi, lo};
#else
    return umul_genetic(x, y);
#endif
}

inline uint128 operator*(const uint128& x, const uint128& y) noexcept
{
    auto p = umul(x.lo, y.lo);
    p.hi += (x.lo * y.hi) + (x.hi * y.lo);
    return {p.hi, p.lo};
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

inline uint128& operator++(uint128& x) noexcept
{
    return x += 1;
}

inline uint128& operator--(uint128& x) noexcept
{
    return x -= 1;
}

template <typename T>
struct div_result
{
    T quot;
    T rem;
};

div_result<uint128> udivrem(uint128 x, uint128 y) noexcept;

inline uint128 operator/(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).quot;
}

inline uint128 operator%(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).rem;
}

inline int clz(uint32_t x) noexcept
{
#ifdef _MSC_VER
    unsigned long most_significant_bit;
    _BitScanReverse(&most_significant_bit, x);
    return 31 ^ (int)most_significant_bit;
#else
    return __builtin_clz(x);
#endif
}

inline int clz(uint64_t x) noexcept
{
#ifdef _MSC_VER
    unsigned long most_significant_bit;
    _BitScanReverse64(&most_significant_bit, x);
    return 63 ^ (int)most_significant_bit;
#else
    return __builtin_clzl(x);
#endif
}

inline int clz(const uint128& x)
{
    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    return x.hi == 0 ? clz(x.lo) | 64 : clz(x.hi);
}

namespace internal
{
/// Optimized addition.
///
/// This keeps the multiprecision addition until CodeGen so the pattern is not
/// broken during other optimizations.
constexpr uint128 optimized_add(uint128 x, uint128 y) noexcept
{
#ifdef __SIZEOF_INT128__
    using u128 = unsigned __int128;
    return ((u128(x.hi) << 64) | x.lo) + ((u128(y.hi) << 64) | y.lo);
#else
    return x + y;
#endif
}
}  // namespace internal
}  // namespace intx
