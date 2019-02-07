// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <cstdint>
#include <stdexcept>
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

    // TODO: Would it be enough to have a constructor for uint64_t?
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


/// Linear arithmetic operators.
/// @{

constexpr uint128 operator+(uint128 x, uint128 y) noexcept
{
    return {x.hi + y.hi + (x.lo > (x.lo + y.lo)), x.lo + y.lo};
}

constexpr uint128 operator+(uint128 x) noexcept
{
    return x;
}

constexpr uint128 operator-(uint128 x, uint128 y) noexcept
{
    return {x.hi - y.hi - (x.lo < (x.lo - y.lo)), x.lo - y.lo};
}

constexpr uint128 operator-(uint128 x) noexcept
{
    // Implementing as subtraction is better than ~x + 1.
    // Clang7: Almost perfect.
    // GCC8: Does something weird.
    return 0 - x;
}

inline uint128& operator++(uint128& x) noexcept
{
    return x = x + 1;
}

inline uint128& operator--(uint128& x) noexcept
{
    return x = x - 1;
}

inline uint128 operator++(uint128& x, int) noexcept
{
    auto ret = x;
    ++x;
    return ret;
}

inline uint128 operator--(uint128& x, int) noexcept
{
    auto ret = x;
    --x;
    return ret;
}

/// Optimized addition.
///
/// This keeps the multiprecision addition until CodeGen so the pattern is not
/// broken during other optimizations.
constexpr uint128 fast_add(uint128 x, uint128 y) noexcept
{
#ifdef __SIZEOF_INT128__
    return (unsigned __int128){x} + (unsigned __int128){y};
#else
    // Fallback to regular addition.
    return x + y;
#endif
}

/// @}


/// Bitwise operators.
/// @{

constexpr uint128 operator~(uint128 x) noexcept
{
    return {~x.hi, ~x.lo};
}

constexpr uint128 operator|(uint128 x, uint128 y) noexcept
{
    // Clang7: perfect.
    // GCC8: stupidly uses a vector instruction in all bitwise operators.
    return {x.hi | y.hi, x.lo | y.lo};
}

constexpr uint128 operator&(uint128 x, uint128 y) noexcept
{
    return {x.hi & y.hi, x.lo & y.lo};
}

constexpr uint128 operator^(uint128 x, uint128 y) noexcept
{
    return {x.hi ^ y.hi, x.lo ^ y.lo};
}

constexpr uint128 operator<<(uint128 x, unsigned shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 right shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{(x.hi << shift) | ((x.lo >> 1) >> (63 - shift)), x.lo << shift} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{x.lo << (shift - 64), 0} : 0;
}

constexpr uint128 operator>>(uint128 x, unsigned shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 left shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{x.hi >> shift, (x.lo >> shift) | ((x.hi << 1) << (63 - shift))} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{0, x.hi >> (shift - 64)} : 0;
}

/// @}


/// Comparison operators.
///
/// In all implementations bitwise operators are used instead of logical ones
/// to avoid branching.
///
/// @{

constexpr bool operator==(uint128 x, uint128 y) noexcept
{
    // Clang7: generates perfect xor based code,
    //         much better than __int128 where it uses vector instructions.
    // GCC8: generates a bit worse cmp based code
    //       although it generates the xor based one for __int128.
    return (x.lo == y.lo) & (x.hi == y.hi);
}

constexpr bool operator!=(uint128 x, uint128 y) noexcept
{
    // Analogous to ==, but == not used directly, because that confuses GCC8.
    return (x.lo != y.lo) | (x.hi != y.hi);
}

constexpr bool operator<(uint128 x, uint128 y) noexcept
{
    // OPT: This should be implemented by checking the borrow of x - y,
    //      but compilers (GCC8, Clang7)
    //      have problem with properly optimizing subtraction.
    return (x.hi < y.hi) | ((x.hi == y.hi) & (x.lo < y.lo));
}

constexpr bool operator<=(uint128 x, uint128 y) noexcept
{
    // OPT: This also should be implemented by subtraction + flag check.
    // TODO: Clang7 is not able to fully optimize
    //       the naive implementation as (x < y) | (x == y).
    return (x.hi < y.hi) | ((x.hi == y.hi) & (x.lo <= y.lo));
}

constexpr bool operator>(uint128 x, uint128 y) noexcept
{
    return !(x <= y);
}

constexpr bool operator>=(uint128 x, uint128 y) noexcept
{
    return !(x < y);
}

/// @}


/// Multiplication
/// @{

/// Portable full unsigned multiplication 64 x 64 -> 128.
constexpr uint128 umul_generic(uint64_t x, uint64_t y) noexcept
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

    uint64_t lo = x * y;
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
    return umul_generic(x, y);
#endif
}

inline uint128 operator*(uint128 x, uint128 y) noexcept
{
    auto p = umul(x.lo, y.lo);
    p.hi += (x.lo * y.hi) + (x.hi * y.lo);
    return {p.hi, p.lo};
}

constexpr uint128 constexpr_mul(uint128 x, uint128 y) noexcept
{
    auto p = umul_generic(x.lo, y.lo);
    p.hi += (x.lo * y.hi) + (x.hi * y.lo);
    return {p.hi, p.lo};
}

/// @}


/// Assignment operators.
/// @{

constexpr uint128& operator+=(uint128& x, uint128 y) noexcept
{
    return x = x + y;
}

constexpr uint128& operator-=(uint128& x, uint128 y) noexcept
{
    return x = x - y;
}

inline uint128& operator*=(uint128& x, uint128 y) noexcept
{
    return x = x * y;
}

constexpr uint128& operator|=(uint128& x, uint128 y) noexcept
{
    return x = x | y;
}

constexpr uint128& operator&=(uint128& x, uint128 y) noexcept
{
    return x = x & y;
}

constexpr uint128& operator^=(uint128& x, uint128 y) noexcept
{
    return x = x ^ y;
}

constexpr uint128& operator<<=(uint128& x, unsigned shift) noexcept
{
    return x = x << shift;
}

constexpr uint128& operator>>=(uint128& x, unsigned shift) noexcept
{
    return x = x >> shift;
}

/// @}


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

inline int clz(uint128 x)
{
    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    return x.hi == 0 ? clz(x.lo) | 64 : clz(x.hi);
}


/// Division.
/// @{

template <typename T>
struct div_result
{
    T quot;
    T rem;
};

namespace internal
{
constexpr uint16_t reciprocal_table_item(uint8_t d9) noexcept
{
    return uint16_t(0x7fd00 / (0x100 | d9));
}

#define REPEAT4(x)                                                  \
    reciprocal_table_item((x) + 0), reciprocal_table_item((x) + 1), \
        reciprocal_table_item((x) + 2), reciprocal_table_item((x) + 3)

#define REPEAT32(x)                                                                         \
    REPEAT4((x) + 4 * 0), REPEAT4((x) + 4 * 1), REPEAT4((x) + 4 * 2), REPEAT4((x) + 4 * 3), \
        REPEAT4((x) + 4 * 4), REPEAT4((x) + 4 * 5), REPEAT4((x) + 4 * 6), REPEAT4((x) + 4 * 7)

#define REPEAT256()                                                                           \
    REPEAT32(32 * 0), REPEAT32(32 * 1), REPEAT32(32 * 2), REPEAT32(32 * 3), REPEAT32(32 * 4), \
        REPEAT32(32 * 5), REPEAT32(32 * 6), REPEAT32(32 * 7)

/// Reciprocal lookup table.
constexpr uint16_t reciprocal_table[] = {REPEAT256()};

#undef REPEAT4
#undef REPEAT32
#undef REPEAT256
}  // namespace internal

/// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
///
/// Based on Algorithm 2 from "Improved division by invariant integers".
inline uint64_t reciprocal_2by1(uint64_t d) noexcept
{
    auto d9 = uint8_t(d >> 55);
    auto v0 = uint64_t{internal::reciprocal_table[d9]};

    auto d40 = (d >> 24) + 1;
    auto v1 = (v0 << 11) - (v0 * v0 * d40 >> 40) - 1;

    auto v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    auto d0 = d % 2;
    auto d63 = d / 2 + d0;  // ceil(d/2)
    auto e = ((v2 / 2) & -d0) - v2 * d63;
    auto mh = umul(v2, e).hi;
    auto v3 = (v2 << 31) + (mh >> 1);

    // OPT: The compiler tries a bit too much with 128 + 64 addition and ends up using subtraction.
    //      Compare with __int128.
    auto mf = umul(v3, d);
    auto m = fast_add(mf, d);
    auto v3a = m.hi + d;

    auto v4 = v3 - v3a;

    return v4;
}

inline uint64_t reciprocal_3by2(uint128 d) noexcept
{
    auto v = reciprocal_2by1(d.hi);
    auto p = d.hi * v;
    p += d.lo;
    if (p < d.lo)
    {
        --v;
        if (p >= d.hi)
        {
            --v;
            p -= d.hi;
        }
        p -= d.hi;
    }

    auto t = umul(v, d.lo);

    p += t.hi;
    if (p < t.hi)
    {
        --v;
        if (uint128{p, t.lo} >= d)
            --v;
    }
    return v;
}

inline div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept
{
    auto q = umul(v, u.hi);
    q = fast_add(q, u);

    ++q.hi;

    auto r = u.lo - q.hi * d;

    if (r > q.lo)
    {
        --q.hi;
        r += d;
    }

    if (r >= d)
    {
        ++q.hi;
        r -= d;
    }

    return {q.hi, r};
}

inline div_result<uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint128 d, uint64_t v) noexcept
{
    auto q = umul(v, u2);
    q = fast_add(q, {u2, u1});

    auto r1 = u1 - q.hi * d.hi;

    auto t = umul(d.lo, q.hi);

    auto r = uint128{r1, u0} - t - d;
    r1 = r.hi;

    ++q.hi;

    if (r1 >= q.lo)
    {
        --q.hi;
        r += d;
    }

    if (r >= d)
    {
        ++q.hi;
        r -= d;
    }

    return {q.hi, r};
}

inline div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        auto lsh = clz(y.lo);

        uint64_t xn_ex, xn_hi, xn_lo, yn;

        if (lsh != 0)
        {
            auto rsh = 64 - lsh;
            xn_ex = x.hi >> rsh;
            xn_hi = (x.lo >> rsh) | (x.hi << lsh);
            xn_lo = x.lo << lsh;
            yn = y.lo << lsh;
        }
        else
        {
            xn_ex = 0;
            xn_hi = x.hi;
            xn_lo = x.lo;
            yn = y.lo;
        }

        auto v = reciprocal_2by1(yn);

        // OPT: If xn_ex is 0, the result q can be only 0 or 1.
        auto res = udivrem_2by1({xn_ex, xn_hi}, yn, v);
        auto q1 = res.quot;

        res = udivrem_2by1({res.rem, xn_lo}, yn, v);
        auto q0 = res.quot;

        auto q = uint128{q1, q0};
        return {q, res.rem >> lsh};
    }

    if (y.hi > x.hi)
        return {0, x};

    auto lsh = clz(y.hi);

    if (lsh == 0)
    {
        bool q = (y.hi < x.hi) | (y.lo <= x.lo);
        return {q, x - (q ? y : 0)};
    }

    auto rsh = 64 - lsh;

    auto yn_lo = y.lo << lsh;
    auto yn_hi = (y.lo >> rsh) | (y.hi << lsh);
    auto xn_ex = x.hi >> rsh;
    auto xn_hi = (x.lo >> rsh) | (x.hi << lsh);
    auto xn_lo = x.lo << lsh;

    auto v = reciprocal_3by2({yn_hi, yn_lo});
    auto res = udivrem_3by2(xn_ex, xn_hi, xn_lo, {yn_hi, yn_lo}, v);

    return {res.quot, res.rem >> lsh};
}

inline uint128 operator/(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).quot;
}

inline uint128 operator%(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).rem;
}

inline uint128& operator/=(uint128& x, uint128 y) noexcept
{
    return x = x / y;
}

inline uint128& operator%=(uint128& x, uint128 y) noexcept
{
    return x = x % y;
}

/// @}


constexpr uint128 operator""_u128(const char* s)
{
    using namespace std::literals;

    uint128 x;
    size_t num_digits = 0;

    if (s[0] == '0' && s[1] == 'x')
    {
        s += 2;
        while (auto d = *s++)
        {
            if (++num_digits > sizeof(x) * 2)
                throw std::overflow_error{"Literal overflow"};

            x <<= 4;
            if (d >= '0' && d <= '9')
                d -= '0';
            else if (d >= 'a' && d <= 'f')
                d -= 'a' - 10;
            else if (d >= 'A' && d <= 'F')
                d -= 'A' - 10;
            else
                throw std::invalid_argument{"Invalid literal character: "s + d};
            x += d;
        }
        return x;
    }

    while (auto d = *s++)
    {
        // TODO: std::numeric_limits<uint128>::digits10 can be used here.
        if (++num_digits > 39)
            throw std::overflow_error{"Literal overflow"};

        x = constexpr_mul(x, 10);
        if (d >= '0' && d <= '9')
            d -= '0';
        else
            throw std::invalid_argument{"Invalid literal character: "s + d};
        x += d;
        if (x < d)
            throw std::overflow_error{"Literal overflow"};
    }
    return x;
}

}  // namespace intx
