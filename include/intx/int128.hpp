// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>

#ifndef __has_builtin
    #define __has_builtin(NAME) 0
#endif

#ifdef _MSC_VER
    #include <intrin.h>
#endif

#if !defined(__has_builtin)
    #define __has_builtin(NAME) 0
#endif

#if !defined(__has_feature)
    #define __has_feature(NAME) 0
#endif

#if !defined(NDEBUG)
    #define INTX_UNREACHABLE() assert(false)
#elif __has_builtin(__builtin_unreachable)
    #define INTX_UNREACHABLE() __builtin_unreachable()
#elif defined(_MSC_VER)
    #define INTX_UNREACHABLE() __assume(0)
#else
    #define INTX_UNREACHABLE() (void)0
#endif


#if __has_builtin(__builtin_expect)
    #define INTX_UNLIKELY(EXPR) __builtin_expect(bool{EXPR}, false)
#else
    #define INTX_UNLIKELY(EXPR) (bool{EXPR})
#endif

#if !defined(NDEBUG)
    #define INTX_REQUIRE assert
#else
    #define INTX_REQUIRE(X) (X) ? (void)0 : INTX_UNREACHABLE()
#endif


// Detect compiler support for 128-bit integer __int128
#if defined(__SIZEOF_INT128__)
    #define INTX_HAS_BUILTIN_INT128 1
#else
    #define INTX_HAS_BUILTIN_INT128 0
#endif


namespace intx
{
#if INTX_HAS_BUILTIN_INT128
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wpedantic"  // Usage of __int128 triggers a pedantic warning.

/// Alias for the compiler supported unsigned __int128 type.
using builtin_uint128 = unsigned __int128;

    #pragma GCC diagnostic pop
#endif

template <unsigned N>
struct uint;

struct X
{
    uint64_t l_;
    uint64_t h_;

    constexpr X(uint64_t h, uint64_t l) noexcept : l_{l}, h_{h} {}

    constexpr operator uint<128>() noexcept;
};

/// The 128-bit unsigned integer.
///
/// This type is defined as a specialization of uint<> to easier integration with full intx package,
/// however, uint128 may be used independently.
template <>
struct uint<128>
{
    static constexpr unsigned num_bits = 128;
    static constexpr unsigned num_words = 2;

private:
    uint64_t words_[2]{};

public:
    constexpr uint() noexcept = default;

    // constexpr uint(uint64_t high, uint64_t low) noexcept : words_{low, high} {}

    template <typename T,
        typename = typename std::enable_if_t<std::is_convertible<T, uint64_t>::value>>
    constexpr uint(T x) noexcept : words_{static_cast<uint64_t>(x), 0}  // NOLINT
    {}

#if INTX_HAS_BUILTIN_INT128
    constexpr uint(builtin_uint128 x) noexcept  // NOLINT
      : words_{uint64_t(x), uint64_t(x >> 64)}
    {}

    constexpr explicit operator builtin_uint128() const noexcept
    {
        return (builtin_uint128{words_[1]} << 64) | words_[0];
    }
#endif

    constexpr uint64_t& operator[](size_t i) noexcept { return words_[i]; }
    constexpr const uint64_t& operator[](size_t i) const noexcept { return words_[i]; }

    constexpr explicit operator bool() const noexcept { return (words_[0] | words_[1]) != 0; }

    /// Explicit converting operator for all builtin integral types.
    template <typename Int, typename = typename std::enable_if<std::is_integral<Int>::value>::type>
    constexpr explicit operator Int() const noexcept
    {
        return static_cast<Int>(words_[0]);
    }
};

using uint128 = uint<128>;


constexpr X::operator uint128() noexcept
{
    uint<128> r;
    r[0] = l_;
    r[1] = h_;
    return r;
}

inline constexpr uint64_t hi(uint128 x) noexcept
{
    return x[1];
}
inline constexpr uint64_t lo(uint128 x) noexcept
{
    return x[0];
}

inline constexpr bool is_constant_evaluated() noexcept
{
#if __has_builtin(__builtin_is_constant_evaluated) || (defined(_MSC_VER) && _MSC_VER >= 1925)
    return __builtin_is_constant_evaluated();
#else
    return true;
#endif
}


/// Contains result of add/sub/etc with a carry flag.
template <typename T>
struct result_with_carry
{
    T value;
    bool carry;

    /// Conversion to tuple of references, to allow usage with std::tie().
    constexpr operator std::tuple<T&, bool&>() noexcept { return {value, carry}; }
};


/// Linear arithmetic operators.
/// @{

inline constexpr result_with_carry<uint64_t> add_with_carry(
    uint64_t x, uint64_t y, bool carry = false) noexcept
{
    const auto s = x + y;
    const auto carry1 = s < x;
    const auto t = s + carry;
    const auto carry2 = t < s;
    return {t, carry1 || carry2};
}

template <unsigned N>
inline constexpr result_with_carry<uint<N>> add_with_carry(
    const uint<N>& x, const uint<N>& y, bool carry = false) noexcept
{
    uint<N> s;
    bool k = carry;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
    {
        s[i] = x[i] + y[i];
        const auto k1 = s[i] < x[i];
        s[i] += k;
        k = (s[i] < uint64_t{k}) || k1;
    }
    return {s, k};
}

inline constexpr uint128 operator+(uint128 x, uint128 y) noexcept
{
    return add_with_carry(x, y).value;
}

inline constexpr uint128 operator+(uint128 x) noexcept
{
    return x;
}

inline constexpr result_with_carry<uint64_t> sub_with_carry(
    uint64_t x, uint64_t y, bool carry = false) noexcept
{
    const auto d = x - y;
    const auto carry1 = x < y;
    const auto e = d - carry;
    const auto carry2 = d < uint64_t{carry};
    return {e, carry1 || carry2};
}

/// Performs subtraction of two unsigned numbers and returns the difference
/// and the carry bit (aka borrow, overflow).
template <unsigned N>
inline constexpr result_with_carry<uint<N>> sub_with_carry(
    const uint<N>& x, const uint<N>& y, bool carry = false) noexcept
{
    uint<N> z;
    bool k = carry;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
    {
        z[i] = x[i] - y[i];
        const auto k1 = x[i] < y[i];
        const auto k2 = z[i] < uint64_t{k};
        z[i] -= k;
        k = k1 || k2;
    }
    return {z, k};
}

inline constexpr uint128 operator-(uint128 x, uint128 y) noexcept
{
    return sub_with_carry(x, y).value;
}

inline constexpr uint128 operator-(uint128 x) noexcept
{
    // Implementing as subtraction is better than ~x + 1.
    // Clang9: Perfect.
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
inline constexpr uint128 fast_add(uint128 x, uint128 y) noexcept
{
#if INTX_HAS_BUILTIN_INT128
    return builtin_uint128{x} + builtin_uint128{y};
#else
    return x + y;  // Fallback to generic addition.
#endif
}

/// @}


/// Comparison operators.
///
/// In all implementations bitwise operators are used instead of logical ones
/// to avoid branching.
///
/// @{

inline constexpr bool operator==(uint128 x, uint128 y) noexcept
{
    // Clang7: generates perfect xor based code,
    //         much better than __int128 where it uses vector instructions.
    // GCC8: generates a bit worse cmp based code
    //       although it generates the xor based one for __int128.
    return (x[0] == y[0]) & (x[1] == y[1]);
}

inline constexpr bool operator!=(uint128 x, uint128 y) noexcept
{
    // Analogous to ==, but == not used directly, because that confuses GCC 8-9.
    return (x[0] != y[0]) | (x[1] != y[1]);
}

inline constexpr bool operator<(uint128 x, uint128 y) noexcept
{
    // OPT: This should be implemented by checking the borrow of x - y,
    //      but compilers (GCC8, Clang7)
    //      have problem with properly optimizing subtraction.
    return (x[1] < y[1]) | ((x[1] == y[1]) & (x[0] < y[0]));
}

inline constexpr bool operator<=(uint128 x, uint128 y) noexcept
{
    return !(y < x);
}

inline constexpr bool operator>(uint128 x, uint128 y) noexcept
{
    return y < x;
}

inline constexpr bool operator>=(uint128 x, uint128 y) noexcept
{
    return !(x < y);
}

/// @}


/// Bitwise operators.
/// @{

inline constexpr uint128 operator~(uint128 x) noexcept
{
    return X{~x[1], ~x[0]};
}

inline constexpr uint128 operator|(uint128 x, uint128 y) noexcept
{
    // Clang7: perfect.
    // GCC8: stupidly uses a vector instruction in all bitwise operators.
    return X{x[1] | y[1], x[0] | y[0]};
}

inline constexpr uint128 operator&(uint128 x, uint128 y) noexcept
{
    return X{x[1] & y[1], x[0] & y[0]};
}

inline constexpr uint128 operator^(uint128 x, uint128 y) noexcept
{
    return X{x[1] ^ y[1], x[0] ^ y[0]};
}

inline constexpr uint128 operator<<(uint128 x, uint64_t shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 right shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{X{(x[1] << shift) | ((x[0] >> 1) >> (63 - shift)), x[0] << shift}} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{X{x[0] << (shift - 64), 0}} : 0;
}

inline constexpr uint128 operator<<(uint128 x, uint128 shift) noexcept
{
    if (shift < 128)
        return x << static_cast<uint64_t>(shift);
    return 0;
}

inline constexpr uint128 operator>>(uint128 x, uint64_t shift) noexcept
{
    return (shift < 64) ?
               // Find the part moved from lo to hi.
               // For shift == 0 left shift by (64 - shift) is invalid so
               // split it into 2 shifts by 1 and (63 - shift).
               uint128{X{x[1] >> shift, (x[0] >> shift) | ((x[1] << 1) << (63 - shift))}} :

               // Guarantee "defined" behavior for shifts larger than 128.
               (shift < 128) ? uint128{X{0, x[1] >> (shift - 64)}} : 0;
}

inline constexpr uint128 operator>>(uint128 x, uint128 shift) noexcept
{
    if (shift < 128)
        return x >> static_cast<uint64_t>(shift);
    return 0;
}


/// @}


/// Multiplication
/// @{

/// Full unsigned multiplication 64 x 64 -> 128.
inline constexpr uint128 umul(uint64_t x, uint64_t y) noexcept
{
#if INTX_HAS_BUILTIN_INT128
    return builtin_uint128{x} * builtin_uint128{y};
#elif defined(_MSC_VER) && _MSC_VER >= 1925
    if (!is_constant_evaluated())
    {
        unsigned __int64 hi = 0;
        const auto lo = _umul128(x, y, &hi);
        return X{hi, lo};
    }
    // For constexpr fallback to portable variant.
#endif

    // Portable full unsigned multiplication 64 x 64 -> 128.
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
    return X{hi, lo};
}

inline constexpr uint128 operator*(uint128 x, uint128 y) noexcept
{
    auto p = umul(x[0], y[0]);
    p[1] += (x[0] * y[1]) + (x[1] * y[0]);
    return X{p[1], p[0]};
}

/// @}


/// Assignment operators.
/// @{

inline constexpr uint128& operator+=(uint128& x, uint128 y) noexcept
{
    return x = x + y;
}

inline constexpr uint128& operator-=(uint128& x, uint128 y) noexcept
{
    return x = x - y;
}

inline uint128& operator*=(uint128& x, uint128 y) noexcept
{
    return x = x * y;
}

inline constexpr uint128& operator|=(uint128& x, uint128 y) noexcept
{
    return x = x | y;
}

inline constexpr uint128& operator&=(uint128& x, uint128 y) noexcept
{
    return x = x & y;
}

inline constexpr uint128& operator^=(uint128& x, uint128 y) noexcept
{
    return x = x ^ y;
}

inline constexpr uint128& operator<<=(uint128& x, uint64_t shift) noexcept
{
    return x = x << shift;
}

inline constexpr uint128& operator>>=(uint128& x, uint64_t shift) noexcept
{
    return x = x >> shift;
}

/// @}


inline constexpr unsigned clz_generic(uint32_t x) noexcept
{
    unsigned n = 32;
    for (int i = 4; i >= 0; --i)
    {
        const auto s = unsigned{1} << i;
        const auto hi = x >> s;
        if (hi != 0)
        {
            n -= s;
            x = hi;
        }
    }
    return n - x;
}

inline constexpr unsigned clz_generic(uint64_t x) noexcept
{
    unsigned n = 64;
    for (int i = 5; i >= 0; --i)
    {
        const auto s = unsigned{1} << i;
        const auto hi = x >> s;
        if (hi != 0)
        {
            n -= s;
            x = hi;
        }
    }
    return n - static_cast<unsigned>(x);
}

inline constexpr unsigned clz(uint32_t x) noexcept
{
#ifdef _MSC_VER
    return clz_generic(x);
#else
    return x != 0 ? unsigned(__builtin_clz(x)) : 32;
#endif
}

inline constexpr unsigned clz(uint64_t x) noexcept
{
#ifdef _MSC_VER
    return clz_generic(x);
#else
    return x != 0 ? unsigned(__builtin_clzll(x)) : 64;
#endif
}

inline constexpr unsigned clz(uint128 x) noexcept
{
    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    return x[1] == 0 ? clz(x[0]) + 64 : clz(x[1]);
}


inline constexpr uint64_t bswap(uint64_t x) noexcept
{
#if __has_builtin(__builtin_bswap64)
    return __builtin_bswap64(x);
#else
    #ifdef _MSC_VER
    if (!is_constant_evaluated())
        return _byteswap_uint64(x);
    #endif
    const auto a = ((x << 8) & 0xFF00FF00FF00FF00) | ((x >> 8) & 0x00FF00FF00FF00FF);
    const auto b = ((a << 16) & 0xFFFF0000FFFF0000) | ((a >> 16) & 0x0000FFFF0000FFFF);
    return (b << 32) | (b >> 32);
#endif
}

inline constexpr uint128 bswap(uint128 x) noexcept
{
    return X{bswap(x[0]), bswap(x[1])};
}


/// Division.
/// @{

template <typename QuotT, typename RemT = QuotT>
struct div_result
{
    QuotT quot;
    RemT rem;

    /// Conversion to tuple of references, to allow usage with std::tie().
    constexpr operator std::tuple<QuotT&, RemT&>() noexcept { return {quot, rem}; }
};

namespace internal
{
inline constexpr uint16_t reciprocal_table_item(uint8_t d9) noexcept
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
    INTX_REQUIRE(d & 0x8000000000000000);  // Must be normalized.

    const uint64_t d9 = d >> 55;
    const uint32_t v0 = internal::reciprocal_table[d9 - 256];

    const uint64_t d40 = (d >> 24) + 1;
    const uint64_t v1 = (v0 << 11) - uint32_t(v0 * v0 * d40 >> 40) - 1;

    const uint64_t v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    const uint64_t d0 = d & 1;
    const uint64_t d63 = (d >> 1) + d0;  // ceil(d/2)
    const uint64_t e = ((v2 >> 1) & (0 - d0)) - v2 * d63;
    const uint64_t v3 = (umul(v2, e)[1] >> 1) + (v2 << 31);

    const uint64_t v4 = v3 - (umul(v3, d) + d)[1] - d;
    return v4;
}

inline uint64_t reciprocal_3by2(uint128 d) noexcept
{
    auto v = reciprocal_2by1(d[1]);
    auto p = d[1] * v;
    p += d[0];
    if (p < d[0])
    {
        --v;
        if (p >= d[1])
        {
            --v;
            p -= d[1];
        }
        p -= d[1];
    }

    const auto t = umul(v, d[0]);

    p += t[1];
    if (p < t[1])
    {
        --v;
        if (p >= d[1])
        {
            if (p > d[1] || t[0] >= d[0])
                --v;
        }
    }
    return v;
}

inline div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept
{
    auto q = umul(v, u[1]);
    q = fast_add(q, u);

    ++q[1];

    auto r = u[0] - q[1] * d;

    if (r > q[0])
    {
        --q[1];
        r += d;
    }

    if (r >= d)
    {
        ++q[1];
        r -= d;
    }

    return {q[1], r};
}

inline div_result<uint64_t, uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint128 d, uint64_t v) noexcept
{
    auto q = umul(v, u2);
    q = fast_add(q, X{u2, u1});

    auto r1 = u1 - q[1] * d[1];

    auto t = umul(d[0], q[1]);

    auto r = uint128{X{r1, u0}} - t - d;
    r1 = r[1];

    ++q[1];

    if (r1 >= q[0])
    {
        --q[1];
        r += d;
    }

    if (r >= d)
    {
        ++q[1];
        r -= d;
    }

    return {q[1], r};
}

inline div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
{
    if (y[1] == 0)
    {
        INTX_REQUIRE(y[0] != 0);  // Division by 0.

        const auto lsh = clz(y[0]);
        const auto rsh = (64 - lsh) % 64;
        const auto rsh_mask = uint64_t{lsh == 0} - 1;

        const auto yn = y[0] << lsh;
        const auto xn_lo = x[0] << lsh;
        const auto xn_hi = (x[1] << lsh) | ((x[0] >> rsh) & rsh_mask);
        const auto xn_ex = (x[1] >> rsh) & rsh_mask;

        const auto v = reciprocal_2by1(yn);
        const auto res1 = udivrem_2by1(X{xn_ex, xn_hi}, yn, v);
        const auto res2 = udivrem_2by1(X{res1.rem, xn_lo}, yn, v);
        return {X{res1.quot, res2.quot}, res2.rem >> lsh};
    }

    if (y[1] > x[1])
        return {0, x};

    const auto lsh = clz(y[1]);
    if (lsh == 0)
    {
        const auto q = unsigned{y[1] < x[1]} | unsigned{y[0] <= x[0]};
        return {q, x - (q ? y : 0)};
    }

    const auto rsh = 64 - lsh;

    const auto yn_lo = y[0] << lsh;
    const auto yn_hi = (y[1] << lsh) | (y[0] >> rsh);
    const auto xn_lo = x[0] << lsh;
    const auto xn_hi = (x[1] << lsh) | (x[0] >> rsh);
    const auto xn_ex = x[1] >> rsh;

    const auto v = reciprocal_3by2(X{yn_hi, yn_lo});
    const auto res = udivrem_3by2(xn_ex, xn_hi, xn_lo, X{yn_hi, yn_lo}, v);

    return {res.quot, res.rem >> lsh};
}

inline div_result<uint128> sdivrem(uint128 x, uint128 y) noexcept
{
    constexpr auto sign_mask = uint128{1} << 127;
    const auto x_is_neg = (x & sign_mask) != 0;
    const auto y_is_neg = (y & sign_mask) != 0;

    const auto x_abs = x_is_neg ? -x : x;
    const auto y_abs = y_is_neg ? -y : y;

    const auto q_is_neg = x_is_neg ^ y_is_neg;

    const auto res = udivrem(x_abs, y_abs);

    return {q_is_neg ? -res.quot : res.quot, x_is_neg ? -res.rem : res.rem};
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

}  // namespace intx


namespace std
{
template <unsigned N>
struct numeric_limits<intx::uint<N>>
{
    using type = intx::uint<N>;

    static constexpr bool is_specialized = true;
    static constexpr bool is_integer = true;
    static constexpr bool is_signed = false;
    static constexpr bool is_exact = true;
    static constexpr bool has_infinity = false;
    static constexpr bool has_quiet_NaN = false;
    static constexpr bool has_signaling_NaN = false;
    static constexpr float_denorm_style has_denorm = denorm_absent;
    static constexpr bool has_denorm_loss = false;
    static constexpr float_round_style round_style = round_toward_zero;
    static constexpr bool is_iec559 = false;
    static constexpr bool is_bounded = true;
    static constexpr bool is_modulo = true;
    static constexpr int digits = CHAR_BIT * sizeof(type);
    static constexpr int digits10 = int(0.3010299956639812 * digits);
    static constexpr int max_digits10 = 0;
    static constexpr int radix = 2;
    static constexpr int min_exponent = 0;
    static constexpr int min_exponent10 = 0;
    static constexpr int max_exponent = 0;
    static constexpr int max_exponent10 = 0;
    static constexpr bool traps = std::numeric_limits<unsigned>::traps;
    static constexpr bool tinyness_before = false;

    static constexpr type min() noexcept { return 0; }
    static constexpr type lowest() noexcept { return min(); }
    static constexpr type max() noexcept { return ~type{0}; }
    static constexpr type epsilon() noexcept { return 0; }
    static constexpr type round_error() noexcept { return 0; }
    static constexpr type infinity() noexcept { return 0; }
    static constexpr type quiet_NaN() noexcept { return 0; }
    static constexpr type signaling_NaN() noexcept { return 0; }
    static constexpr type denorm_min() noexcept { return 0; }
};
}  // namespace std

namespace intx
{
template <typename T>
[[noreturn]] inline void throw_(const char* what)
{
#if __cpp_exceptions
    throw T{what};
#else
    std::fputs(what, stderr);
    std::abort();
#endif
}

inline constexpr int from_dec_digit(char c)
{
    if (c < '0' || c > '9')
        throw_<std::invalid_argument>("invalid digit");
    return c - '0';
}

inline constexpr int from_hex_digit(char c)
{
    if (c >= 'a' && c <= 'f')
        return c - ('a' - 10);
    if (c >= 'A' && c <= 'F')
        return c - ('A' - 10);
    return from_dec_digit(c);
}

template <typename Int>
inline constexpr Int from_string(const char* str)
{
    auto s = str;
    auto x = Int{};
    int num_digits = 0;

    if (s[0] == '0' && s[1] == 'x')
    {
        s += 2;
        while (const auto c = *s++)
        {
            if (++num_digits > int{sizeof(x) * 2})
                throw_<std::out_of_range>(str);
            x = (x << 4) | from_hex_digit(c);
        }
        return x;
    }

    while (const auto c = *s++)
    {
        if (num_digits++ > std::numeric_limits<Int>::digits10)
            throw_<std::out_of_range>(str);

        const auto d = from_dec_digit(c);
        x = x * Int{10} + d;
        if (x < d)
            throw_<std::out_of_range>(str);
    }
    return x;
}

template <typename Int>
inline constexpr Int from_string(const std::string& s)
{
    return from_string<Int>(s.c_str());
}

inline constexpr uint128 operator""_u128(const char* s)
{
    return from_string<uint128>(s);
}

template <unsigned N>
inline std::string to_string(uint<N> x, int base = 10)
{
    if (base < 2 || base > 36)
        throw_<std::invalid_argument>("invalid base");

    if (x == 0)
        return "0";

    auto s = std::string{};
    while (x != 0)
    {
        // TODO: Use constexpr udivrem_1?
        const auto res = udivrem(x, uint<N>{base});
        const auto d = int(res.rem);
        const auto c = d < 10 ? '0' + d : 'a' + d - 10;
        s.push_back(char(c));
        x = res.quot;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

template <unsigned N>
inline std::string hex(uint<N> x)
{
    return to_string(x, 16);
}
}  // namespace intx
