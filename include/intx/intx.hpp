// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/int128.hpp>
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <limits>
#include <type_traits>

namespace intx
{
template <unsigned N>
struct uint
{
    static_assert((N & (N - 1)) == 0, "Number of bits must be power of 2");
    static_assert(N >= 256, "Number of bits must be at lest 256");

    using word_type = uint64_t;

    /// The 2x smaller type.
    using half_type = uint<N / 2>;

    static constexpr auto num_bits = N;
    static constexpr auto num_words = N / 8 / sizeof(word_type);

private:
    uint64_t words_[num_words]{};

public:
    constexpr uint() noexcept = default;

    /// TODO: deprecated.
    static constexpr uint from_halves(half_type low, half_type high) noexcept
    {
        uint result;
        for (size_t i = 0; i < num_words / 2; ++i)
            result.words_[i] = low[i];
        for (size_t i = 0; i < num_words / 2; ++i)
            result.words_[num_words / 2 + i] = high[i];
        return result;
    }

    /// Implicit converting constructor for the half type.
    constexpr uint(half_type x) noexcept  // NOLINT
    {
        for (size_t i = 0; i < num_words / 2; ++i)
            words_[i] = x[i];
    }

    /// Implicit converting constructor for types convertible to the half type.
    template <typename T,
        typename = typename std::enable_if<std::is_convertible<T, half_type>::value>::type>
    constexpr uint(T x) noexcept  // NOLINT
    {
        half_type l{x};
        for (size_t i = 0; i < num_words / 2; ++i)
            words_[i] = l[i];
    }

    template <typename... T,
        typename = std::enable_if_t<sizeof...(T) == num_words &&
                                    std::conjunction_v<std::is_convertible<T, uint64_t>...>>>
    constexpr uint(T... v) noexcept : words_{static_cast<uint64_t>(v)...}
    {}

    constexpr uint64_t& operator[](size_t i) noexcept { return words_[i]; }

    constexpr const uint64_t& operator[](size_t i) const noexcept { return words_[i]; }

    constexpr explicit operator bool() const noexcept { return *this != uint{}; }

    /// Explicit converting operator for all builtin integral types.
    template <typename Int, typename = typename std::enable_if<std::is_integral<Int>::value>::type>
    explicit operator Int() const noexcept
    {
        // FIXME: Simplify this.
        return static_cast<Int>(lo(*this));
    }
};

using uint256 = uint<256>;
using uint512 = uint<512>;

inline constexpr uint8_t lo(uint16_t x)
{
    return static_cast<uint8_t>(x);
}

inline constexpr uint16_t lo(uint32_t x)
{
    return static_cast<uint16_t>(x);
}

inline constexpr uint32_t lo(uint64_t x)
{
    return static_cast<uint32_t>(x);
}

inline constexpr uint8_t hi(uint16_t x)
{
    return static_cast<uint8_t>(x >> 8);
}

inline constexpr uint16_t hi(uint32_t x)
{
    return static_cast<uint16_t>(x >> 16);
}

inline constexpr uint32_t hi(uint64_t x)
{
    return static_cast<uint32_t>(x >> 32);
}

template <unsigned N>
inline constexpr auto lo(const uint<N>& x) noexcept
{
    uint<N / 2> l;
    for (size_t i = 0; i < decltype(l)::num_words; ++i)
        l[i] = x[i];
    return l;
}

template <unsigned N>
inline constexpr auto hi(const uint<N>& x) noexcept
{
    uint<N / 2> h;
    constexpr auto half_words = decltype(h)::num_words;
    for (size_t i = 0; i < half_words; ++i)
        h[i] = x[half_words + i];
    return h;
}

template <typename T>
inline constexpr unsigned num_bits(const T&) noexcept
{
    return sizeof(T) * 8;
}

template <unsigned N>
inline constexpr bool operator==(const uint<N>& x, const uint<N>& y) noexcept
{
    bool result = true;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        result &= (x[i] == y[i]);
    return result;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator==(const uint<N>& x, const T& y) noexcept
{
    return x == uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator==(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(y) == x;
}


template <unsigned N>
inline constexpr bool operator!=(const uint<N>& x, const uint<N>& y) noexcept
{
    return !(x == y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator!=(const uint<N>& x, const T& y) noexcept
{
    return x != uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator!=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) != y;
}


template <unsigned N>
inline constexpr bool operator<(const uint<N>& x, const uint<N>& y) noexcept
{
    return sub_with_carry(x, y).carry;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator<(const uint<N>& x, const T& y) noexcept
{
    return x < uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator<(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) < y;
}


template <unsigned N>
inline constexpr bool operator>(const uint<N>& x, const uint<N>& y) noexcept
{
    return sub_with_carry(y, x).carry;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator>(const uint<N>& x, const T& y) noexcept
{
    return x > uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator>(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) > y;
}


template <unsigned N>
inline constexpr bool operator>=(const uint<N>& x, const uint<N>& y) noexcept
{
    return !sub_with_carry(x, y).carry;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator>=(const uint<N>& x, const T& y) noexcept
{
    return x >= uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator>=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) >= y;
}


template <unsigned N>
inline constexpr bool operator<=(const uint<N>& x, const uint<N>& y) noexcept
{
    return !sub_with_carry(y, x).carry;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator<=(const uint<N>& x, const T& y) noexcept
{
    return x <= uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr bool operator<=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) <= y;
}

template <unsigned N>
inline constexpr uint<N> operator|(const uint<N>& x, const uint<N>& y) noexcept
{
    uint<N> z;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        z[i] = x[i] | y[i];
    return z;
}

template <unsigned N>
inline constexpr uint<N> operator&(const uint<N>& x, const uint<N>& y) noexcept
{
    uint<N> z;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        z[i] = x[i] & y[i];
    return z;
}

template <unsigned N>
inline constexpr uint<N> operator^(const uint<N>& x, const uint<N>& y) noexcept
{
    uint<N> z;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        z[i] = x[i] ^ y[i];
    return z;
}

template <unsigned N>
inline constexpr uint<N> operator~(const uint<N>& x) noexcept
{
    uint<N> z;
    for (size_t i = 0; i < uint<N>::num_words; ++i)
        z[i] = ~x[i];
    return z;
}

template <unsigned N>
inline constexpr uint<N> operator<<(const uint<N>& x, uint64_t shift) noexcept
{
    constexpr auto word_bits = sizeof(uint64_t) * 8;

    const auto s = shift % word_bits;
    const auto skip = static_cast<size_t>(shift / word_bits);

    uint<N> r;
    uint64_t carry = 0;
    for (size_t i = 0; i < (uint<N>::num_words - skip); ++i)
    {
        r[i + skip] = (x[i] << s) | carry;
        carry = (x[i] >> (word_bits - s - 1)) >> 1;
    }
    return r;
}


template <unsigned N>
inline constexpr uint<N> operator>>(const uint<N>& x, uint64_t shift) noexcept
{
    constexpr auto num_bits = N;
    constexpr auto half_bits = num_bits / 2;

    if (shift < half_bits)
    {
        const auto h = hi(x) >> shift;

        // Find the part moved from hi to lo.
        // To avoid invalid shift left,
        // split them into 2 valid shifts by (lshift - 1) and 1.
        const auto lshift = half_bits - shift;
        const auto h_overflow = (hi(x) << (lshift - 1)) << 1;
        const auto l_part = lo(x) >> shift;
        const auto l = l_part | h_overflow;
        return uint<N>::from_halves(l, h);
    }

    if (shift < num_bits)
        return hi(x) >> (shift - half_bits);

    return 0;
}


template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator<<(const uint<N>& x, const T& shift) noexcept
{
    if (shift < T{sizeof(x) * 8})
        return x << static_cast<uint64_t>(shift);
    return 0;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator>>(const uint<N>& x, const T& shift) noexcept
{
    if (shift < T{sizeof(x) * 8})
        return x >> static_cast<uint64_t>(shift);
    return 0;
}

template <unsigned N>
inline constexpr uint<N>& operator>>=(uint<N>& x, uint64_t shift) noexcept
{
    return x = x >> shift;
}


inline constexpr uint64_t* as_words(uint128& x) noexcept
{
    return &x[0];
}

inline constexpr const uint64_t* as_words(const uint128& x) noexcept
{
    return &x[0];
}

template <unsigned N>
inline constexpr uint64_t* as_words(uint<N>& x) noexcept
{
    return &x[0];
}

template <unsigned N>
inline constexpr const uint64_t* as_words(const uint<N>& x) noexcept
{
    return &x[0];
}

template <unsigned N>
inline uint8_t* as_bytes(uint<N>& x) noexcept
{
    return reinterpret_cast<uint8_t*>(as_words(x));
}

template <unsigned N>
inline const uint8_t* as_bytes(const uint<N>& x) noexcept
{
    return reinterpret_cast<const uint8_t*>(as_words(x));
}

template <unsigned N>
inline constexpr uint<N> operator+(const uint<N>& x, const uint<N>& y) noexcept
{
    return add_with_carry(x, y).value;
}

template <unsigned N>
inline constexpr uint<N> operator-(const uint<N>& x) noexcept
{
    return ~x + uint<N>{1};
}

template <unsigned N>
inline constexpr uint<N> operator-(const uint<N>& x, const uint<N>& y) noexcept
{
    return sub_with_carry(x, y).value;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator+=(uint<N>& x, const T& y) noexcept
{
    return x = x + y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator-=(uint<N>& x, const T& y) noexcept
{
    return x = x - y;
}

template <unsigned N>
inline constexpr uint<N> sqr(const uint<N>& x) noexcept
{
    // Based on recursive multiplication implementation.
    const auto t = umul(lo(x), lo(x));
    const auto h = ((lo(x) * hi(x)) << 1) + hi(t);
    return uint<N>::from_halves(lo(t), h);
}


template <unsigned N>
inline constexpr uint<2 * N> umul(const uint<N>& x, const uint<N>& y) noexcept
{
    constexpr auto num_words = uint<N>::num_words;

    uint<2 * N> p;
    for (size_t j = 0; j < num_words; ++j)
    {
        uint64_t k = 0;
        for (size_t i = 0; i < num_words; ++i)
        {
            const auto t = umul(x[i], y[j]) + p[i + j] + k;
            p[i + j] = t[0];
            k = t[1];
        }
        p[j + num_words] = k;
    }
    return p;
}

/// Multiplication implementation using word access
/// and discarding the high part of the result product.
template <unsigned N>
inline constexpr uint<N> operator*(const uint<N>& x, const uint<N>& y) noexcept
{
    constexpr auto num_words = uint<N>::num_words;

    uint<N> p;
    for (size_t j = 0; j < num_words; j++)
    {
        uint64_t k = 0;
        for (size_t i = 0; i < (num_words - j - 1); i++)
        {
            const auto t = umul(x[i], y[j]) + p[i + j] + k;
            p[i + j] = lo(t);
            k = hi(t);
        }
        p[num_words - 1] += x[num_words - j - 1] * y[j] + k;
    }
    return p;
}


template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator*=(uint<N>& x, const T& y) noexcept
{
    return x = x * y;
}

template <unsigned N>
inline constexpr uint<N> exp(uint<N> base, uint<N> exponent) noexcept
{
    auto result = uint<N>{1};
    if (base == 2)
        return result << exponent;

    while (exponent != 0)
    {
        if ((exponent & 1) != 0)
            result *= base;
        base = sqr(base);
        exponent >>= 1;
    }
    return result;
}

template <unsigned N>
inline constexpr unsigned count_significant_words(const uint<N>& x) noexcept
{
    for (size_t i = uint<N>::num_words; i > 0; --i)
    {
        if (x[i - 1] != 0)
            return static_cast<unsigned>(i);
    }
    return 0;
}

template <unsigned N>
inline constexpr unsigned clz(const uint<N>& x) noexcept
{
    constexpr unsigned num_words = uint<N>::num_words;
    const auto s = count_significant_words(x);
    if (s == 0)
        return num_words * 64;
    return clz(x[s - 1]) + (num_words - s) * 64;
}

namespace internal
{
/// Counts the number of zero leading bits in nonzero argument x.
inline constexpr unsigned clz_nonzero(uint64_t x) noexcept
{
    INTX_REQUIRE(x != 0);
#ifdef _MSC_VER
    return clz_generic(x);
#else
    return unsigned(__builtin_clzll(x));
#endif
}

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

template <typename IntT>
[[gnu::always_inline]] inline normalized_div_args<IntT::num_bits> normalize(
    const IntT& numerator, const IntT& denominator) noexcept
{
    // FIXME: Make the implementation type independent
    static constexpr auto num_words = IntT::num_words;

    auto* u = as_words(numerator);
    auto* v = as_words(denominator);

    normalized_div_args<IntT::num_bits> na;
    auto* un = as_words(na.numerator);
    auto* vn = as_words(na.divisor);

    auto& m = na.num_numerator_words;
    for (m = num_words; m > 0 && u[m - 1] == 0; --m)
        ;

    auto& n = na.num_divisor_words;
    for (n = num_words; n > 0 && v[n - 1] == 0; --n)
        ;

    na.shift = clz_nonzero(v[n - 1]);  // Use clz_nonzero() to avoid clang analyzer's warning.
    if (na.shift)
    {
        for (int i = num_words - 1; i > 0; --i)
            vn[i] = (v[i] << na.shift) | (v[i - 1] >> (64 - na.shift));
        vn[0] = v[0] << na.shift;

        un[num_words] = u[num_words - 1] >> (64 - na.shift);
        for (int i = num_words - 1; i > 0; --i)
            un[i] = (u[i] << na.shift) | (u[i - 1] >> (64 - na.shift));
        un[0] = u[0] << na.shift;
    }
    else
    {
        na.numerator_ex = 0;
        na.numerator = numerator;
        na.divisor = denominator;
    }

    // Skip the highest word of numerator if not significant.
    if (un[m] != 0 || un[m - 1] >= vn[n - 1])
        ++m;

    return na;
}

/// Divides arbitrary long unsigned integer by 64-bit unsigned integer (1 word).
/// @param u    The array of a normalized numerator words. It will contain
///             the quotient after execution.
/// @param len  The number of numerator words.
/// @param d    The normalized divisor.
/// @return     The remainder.
inline uint64_t udivrem_by1(uint64_t u[], int len, uint64_t d) noexcept
{
    INTX_REQUIRE(len >= 2);

    const auto reciprocal = reciprocal_2by1(d);

    auto rem = u[len - 1];  // Set the top word as remainder.
    u[len - 1] = 0;         // Reset the word being a part of the result quotient.

    auto it = &u[len - 2];
    do
    {
        std::tie(*it, rem) = udivrem_2by1(X{rem, *it}, d, reciprocal);
    } while (it-- != &u[0]);

    return rem;
}

/// Divides arbitrary long unsigned integer by 128-bit unsigned integer (2 words).
/// @param u    The array of a normalized numerator words. It will contain the
///             quotient after execution.
/// @param len  The number of numerator words.
/// @param d    The normalized divisor.
/// @return     The remainder.
inline uint128 udivrem_by2(uint64_t u[], int len, uint128 d) noexcept
{
    INTX_REQUIRE(len >= 3);

    const auto reciprocal = reciprocal_3by2(d);

    auto rem = uint128{X{u[len - 1], u[len - 2]}};  // Set the 2 top words as remainder.
    u[len - 1] = u[len - 2] = 0;  // Reset these words being a part of the result quotient.

    auto it = &u[len - 3];
    do
    {
        std::tie(*it, rem) = udivrem_3by2(rem[1], rem[0], *it, d, reciprocal);
    } while (it-- != &u[0]);

    return rem;
}

/// s = x + y.
inline bool add(uint64_t s[], const uint64_t x[], const uint64_t y[], int len) noexcept
{
    // OPT: Add MinLen template parameter and unroll first loop iterations.
    INTX_REQUIRE(len >= 2);

    bool carry = false;
    for (int i = 0; i < len; ++i)
        std::tie(s[i], carry) = add_with_carry(x[i], y[i], carry);
    return carry;
}

/// r = x - multiplier * y.
inline uint64_t submul(
    uint64_t r[], const uint64_t x[], const uint64_t y[], int len, uint64_t multiplier) noexcept
{
    // OPT: Add MinLen template parameter and unroll first loop iterations.
    INTX_REQUIRE(len >= 1);

    uint64_t borrow = 0;
    for (int i = 0; i < len; ++i)
    {
        const auto s = sub_with_carry(x[i], borrow);
        const auto p = umul(y[i], multiplier);
        const auto t = sub_with_carry(s.value, p[0]);
        r[i] = t.value;
        borrow = p[1] + s.carry + t.carry;
    }
    return borrow;
}

inline void udivrem_knuth(
    uint64_t q[], uint64_t u[], int ulen, const uint64_t d[], int dlen) noexcept
{
    INTX_REQUIRE(dlen >= 3);
    INTX_REQUIRE(ulen >= dlen);

    const auto divisor = uint128{X{d[dlen - 1], d[dlen - 2]}};
    const auto reciprocal = reciprocal_3by2(divisor);
    for (int j = ulen - dlen - 1; j >= 0; --j)
    {
        const auto u2 = u[j + dlen];
        const auto u1 = u[j + dlen - 1];
        const auto u0 = u[j + dlen - 2];

        uint64_t qhat;
        if (INTX_UNLIKELY((uint128{X{u2, u1}}) == divisor))  // Division overflows.
        {
            qhat = ~uint64_t{0};

            u[j + dlen] = u2 - submul(&u[j], &u[j], d, dlen, qhat);
        }
        else
        {
            uint128 rhat;
            std::tie(qhat, rhat) = udivrem_3by2(u2, u1, u0, divisor, reciprocal);

            bool carry;
            const auto overflow = submul(&u[j], &u[j], d, dlen - 2, qhat);
            std::tie(u[j + dlen - 2], carry) = sub_with_carry(rhat[0], overflow);
            std::tie(u[j + dlen - 1], carry) = sub_with_carry(rhat[1], carry);

            if (INTX_UNLIKELY(carry))
            {
                --qhat;
                u[j + dlen - 1] += divisor[1] + add(&u[j], &u[j], d, dlen - 1);
            }
        }

        q[j] = qhat;  // Store quotient digit.
    }
}

}  // namespace internal

template <unsigned N>
div_result<uint<N>> udivrem(const uint<N>& u, const uint<N>& v) noexcept
{
    auto na = internal::normalize(u, v);

    if (na.num_numerator_words <= na.num_divisor_words)
        return {0, u};

    if (na.num_divisor_words == 1)
    {
        const auto r = internal::udivrem_by1(
            as_words(na.numerator), na.num_numerator_words, as_words(na.divisor)[0]);
        return {na.numerator, r >> na.shift};
    }

    if (na.num_divisor_words == 2)
    {
        const auto d = as_words(na.divisor);
        const auto r =
            internal::udivrem_by2(as_words(na.numerator), na.num_numerator_words, X{d[1], d[0]});
        return {na.numerator, r >> na.shift};
    }

    auto un = as_words(na.numerator);  // Will be modified.

    uint<N> q;
    internal::udivrem_knuth(
        as_words(q), &un[0], na.num_numerator_words, as_words(na.divisor), na.num_divisor_words);

    uint<N> r;
    auto rw = as_words(r);
    for (int i = 0; i < na.num_divisor_words - 1; ++i)
        rw[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];
    rw[na.num_divisor_words - 1] = un[na.num_divisor_words - 1] >> na.shift;

    return {q, r};
}

template <unsigned N>
inline constexpr div_result<uint<N>> sdivrem(const uint<N>& u, const uint<N>& v) noexcept
{
    const auto sign_mask = uint<N>{1} << (sizeof(u) * 8 - 1);
    auto u_is_neg = (u & sign_mask) != 0;
    auto v_is_neg = (v & sign_mask) != 0;

    auto u_abs = u_is_neg ? -u : u;
    auto v_abs = v_is_neg ? -v : v;

    auto q_is_neg = u_is_neg ^ v_is_neg;

    auto res = udivrem(u_abs, v_abs);

    return {q_is_neg ? -res.quot : res.quot, u_is_neg ? -res.rem : res.rem};
}

template <unsigned N>
inline constexpr uint<N> operator/(const uint<N>& x, const uint<N>& y) noexcept
{
    return udivrem(x, y).quot;
}

template <unsigned N>
inline constexpr uint<N> operator%(const uint<N>& x, const uint<N>& y) noexcept
{
    return udivrem(x, y).rem;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator/=(uint<N>& x, const T& y) noexcept
{
    return x = x / y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator%=(uint<N>& x, const T& y) noexcept
{
    return x = x % y;
}

template <unsigned N>
inline constexpr uint<N> bswap(const uint<N>& x) noexcept
{
    constexpr auto num_words = uint<N>::num_words;
    uint<N> z;
    for (size_t i = 0; i < num_words; ++i)
        z[num_words - 1 - i] = bswap(x[i]);
    return z;
}


// Support for type conversions for binary operators.

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator+(const uint<N>& x, const T& y) noexcept
{
    return x + uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator+(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) + y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator-(const uint<N>& x, const T& y) noexcept
{
    return x - uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator-(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) - y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator*(const uint<N>& x, const T& y) noexcept
{
    return x * uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator*(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) * y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator/(const uint<N>& x, const T& y) noexcept
{
    return x / uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator/(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) / y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator%(const uint<N>& x, const T& y) noexcept
{
    return x % uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator%(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) % y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator|(const uint<N>& x, const T& y) noexcept
{
    return x | uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator|(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) | y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator&(const uint<N>& x, const T& y) noexcept
{
    return x & uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator&(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) & y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator^(const uint<N>& x, const T& y) noexcept
{
    return x ^ uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N> operator^(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) ^ y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator|=(uint<N>& x, const T& y) noexcept
{
    return x = x | y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator&=(uint<N>& x, const T& y) noexcept
{
    return x = x & y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator^=(uint<N>& x, const T& y) noexcept
{
    return x = x ^ y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator<<=(uint<N>& x, const T& y) noexcept
{
    return x = x << y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
inline constexpr uint<N>& operator>>=(uint<N>& x, const T& y) noexcept
{
    return x = x >> y;
}


inline uint256 addmod(const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    const auto s = add_with_carry(x, y);
    uint512 n = s.value;
    n[4] = s.carry;
    return lo(n % mod);
}

inline uint256 mulmod(const uint256& x, const uint256& y, const uint256& mod) noexcept
{
    return lo(umul(x, y) % mod);
}


inline constexpr uint256 operator"" _u256(const char* s) noexcept
{
    return from_string<uint256>(s);
}

inline constexpr uint512 operator"" _u512(const char* s) noexcept
{
    return from_string<uint512>(s);
}

namespace le  // Conversions to/from LE bytes.
{
template <typename IntT, unsigned M>
inline IntT load(const uint8_t (&bytes)[M]) noexcept
{
    static_assert(M == IntT::num_bits / 8,
        "the size of source bytes must match the size of the destination uint");
    auto x = IntT{};
    std::memcpy(&x, bytes, sizeof(x));
    return x;
}

template <unsigned N>
inline void store(uint8_t (&dst)[N / 8], const intx::uint<N>& x) noexcept
{
    std::memcpy(dst, &x, sizeof(x));
}

}  // namespace le


namespace be  // Conversions to/from BE bytes.
{
/// Loads an uint value from bytes of big-endian order.
/// If the size of bytes is smaller than the result uint, the value is zero-extended.
template <typename IntT, unsigned M>
inline IntT load(const uint8_t (&bytes)[M]) noexcept
{
    static_assert(M <= IntT::num_bits / 8,
        "the size of source bytes must not exceed the size of the destination uint");
    auto x = IntT{};
    std::memcpy(&as_bytes(x)[IntT::num_bits / 8 - M], bytes, M);
    return bswap(x);
}

template <typename IntT, typename T>
inline IntT load(const T& t) noexcept
{
    return load<IntT>(t.bytes);
}

/// Stores an uint value in a bytes array in big-endian order.
template <unsigned N>
inline void store(uint8_t (&dst)[N / 8], const intx::uint<N>& x) noexcept
{
    const auto d = bswap(x);
    std::memcpy(dst, &d, sizeof(d));
}

/// Stores an uint value in .bytes field of type T. The .bytes must be an array of uint8_t
/// of the size matching the size of uint.
template <typename T, unsigned N>
inline T store(const intx::uint<N>& x) noexcept
{
    T r{};
    store(r.bytes, x);
    return r;
}

/// Stores the truncated value of an uint in a bytes array.
/// Only the least significant bytes from big-endian representation of the uint
/// are stored in the result bytes array up to array's size.
template <unsigned M, unsigned N>
inline void trunc(uint8_t (&dst)[M], const intx::uint<N>& x) noexcept
{
    static_assert(M < N / 8, "destination must be smaller than the source value");
    const auto d = bswap(x);
    const auto b = as_bytes(d);
    std::memcpy(dst, &b[sizeof(d) - M], M);
}

/// Stores the truncated value of an uint in the .bytes field of an object of type T.
template <typename T, unsigned N>
inline T trunc(const intx::uint<N>& x) noexcept
{
    T r{};
    trunc(r.bytes, x);
    return r;
}

namespace unsafe
{
/// Loads an uint value from a buffer. The user must make sure
/// that the provided buffer is big enough. Therefore marked "unsafe".
template <typename IntT>
inline IntT load(const uint8_t* bytes) noexcept
{
    auto x = IntT{};
    std::memcpy(&x, bytes, sizeof(x));
    return bswap(x);
}

/// Stores an uint value at the provided pointer in big-endian order. The user must make sure
/// that the provided buffer is big enough to fit the value. Therefore marked "unsafe".
template <unsigned N>
inline void store(uint8_t* dst, const intx::uint<N>& x) noexcept
{
    const auto d = bswap(x);
    std::memcpy(dst, &d, sizeof(d));
}
}  // namespace unsafe

}  // namespace be

}  // namespace intx
