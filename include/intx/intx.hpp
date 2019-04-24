// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/int128.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <limits>
#include <tuple>
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
    ///
    /// In the generic case of uint<N> the half type is just uint<N / 2>,
    /// but we have to handle the uint<256> case differently by using
    /// the external uint128 type.
    using half_type = std::conditional_t<N == 256, uint128, uint<N / 2>>;

    static constexpr auto num_words = N / 8 / sizeof(word_type);


    half_type lo = 0;
    half_type hi = 0;

    constexpr uint() noexcept = default;

    constexpr uint(half_type hi, half_type lo) noexcept : lo(lo), hi(hi) {}

    /// Implicit converting constructor for the half type.
    constexpr uint(half_type x) noexcept : lo(x) {}  // NOLINT

    /// Implicit converting constructor for types convertible to the half type.
    template <typename T,
        typename = typename std::enable_if<std::is_convertible<T, half_type>::value>::type>
    constexpr uint(T x) noexcept : lo(x)  // NOLINT
    {}

    /// Explicit converting operator for all builtin integral types.
    template <typename Int, typename = typename std::enable_if<std::is_integral<Int>::value>::type>
    explicit operator Int() const noexcept
    {
        return static_cast<Int>(lo);
    }
};

using uint256 = uint<256>;
using uint512 = uint<512>;

template <typename T>
struct traits
{
};

template <>
struct traits<uint64_t>
{
    using double_type = uint128;
};

template <>
struct traits<uint128>
{
    using double_type = uint256;
};

template <>
struct traits<uint256>
{
    using double_type = uint512;
};

template <>
struct traits<uint512>
{
};


constexpr uint8_t lo_half(uint16_t x)
{
    return static_cast<uint8_t>(x);
}
constexpr uint16_t lo_half(uint32_t x)
{
    return static_cast<uint16_t>(x);
}


constexpr uint32_t lo_half(uint64_t x)
{
    return static_cast<uint32_t>(x);
}

constexpr uint8_t hi_half(uint16_t x)
{
    return static_cast<uint8_t>(x >> 8);
}

constexpr uint16_t hi_half(uint32_t x)
{
    return static_cast<uint16_t>(x >> 16);
}

constexpr uint32_t hi_half(uint64_t x)
{
    return static_cast<uint32_t>(x >> 32);
}

constexpr uint64_t lo_half(uint128 x)
{
    return x.lo;
}

constexpr uint64_t hi_half(uint128 x)
{
    return x.hi;
}

constexpr uint128 lo_half(uint256 x)
{
    return x.lo;
}

constexpr uint128 hi_half(uint256 x)
{
    return x.hi;
}

constexpr uint256 lo_half(uint512 x)
{
    return x.lo;
}

constexpr uint256 hi_half(uint512 x)
{
    return x.hi;
}

constexpr uint64_t join(uint32_t hi, uint32_t lo)
{
    return (uint64_t(hi) << 32) | lo;
}

constexpr uint128 join(uint64_t hi, uint64_t lo) noexcept
{
    return {hi, lo};
}

template <typename T>
constexpr unsigned num_bits(const T&) noexcept
{
    return sizeof(T) * 8;
}

template <unsigned N>
constexpr bool operator==(const uint<N>& a, const uint<N>& b) noexcept
{
    return (a.lo == b.lo) & (a.hi == b.hi);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator==(const uint<N>& x, const T& y) noexcept
{
    return x == uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator==(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(y) == x;
}


template <unsigned N>
constexpr bool operator!=(const uint<N>& a, const uint<N>& b) noexcept
{
    return !(a == b);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator!=(const uint<N>& x, const T& y) noexcept
{
    return x != uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator!=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) != y;
}


template <unsigned N>
constexpr bool operator<(const uint<N>& a, const uint<N>& b) noexcept
{
    // Bitwise operators are used to implement logic here to avoid branching.
    // It also should make the function smaller, but no proper benchmark has
    // been done.
    return (a.hi < b.hi) | ((a.hi == b.hi) & (a.lo < b.lo));
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator<(const uint<N>& x, const T& y) noexcept
{
    return x < uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator<(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) < y;
}


template <unsigned N>
constexpr bool operator>(const uint<N>& a, const uint<N>& b) noexcept
{
    // Bitwise operators are used to implement logic here to avoid branching.
    // It also should make the function smaller, but no proper benchmark has
    // been done.
    return (a.hi > b.hi) | ((a.hi == b.hi) & (a.lo > b.lo));
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator>(const uint<N>& x, const T& y) noexcept
{
    return x > uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator>(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) > y;
}


template <unsigned N>
constexpr bool operator>=(const uint<N>& a, const uint<N>& b) noexcept
{
    return !(a < b);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator>=(const uint<N>& x, const T& y) noexcept
{
    return x >= uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator>=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) >= y;
}


template <unsigned N>
constexpr bool operator<=(const uint<N>& a, const uint<N>& b) noexcept
{
    return !(a > b);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator<=(const uint<N>& x, const T& y) noexcept
{
    return x <= uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr bool operator<=(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) <= y;
}

template <unsigned N>
constexpr uint<N> operator|(const uint<N>& x, const uint<N>& y) noexcept
{
    return {x.hi | y.hi, x.lo | y.lo};
}

template <unsigned N>
constexpr uint<N> operator&(const uint<N>& x, const uint<N>& y) noexcept
{
    return {x.hi & y.hi, x.lo & y.lo};
}

template <unsigned N>
constexpr uint<N> operator^(const uint<N>& x, const uint<N>& y) noexcept
{
    return {x.hi ^ y.hi, x.lo ^ y.lo};
}

template <unsigned N>
constexpr uint<N> operator~(const uint<N>& x) noexcept
{
    return {~x.hi, ~x.lo};
}

template <unsigned N>
constexpr uint<N> operator<<(const uint<N>& x, unsigned shift) noexcept
{
    constexpr auto num_bits = N;
    constexpr auto half_bits = num_bits / 2;

    if (shift < half_bits)
    {
        const auto lo = x.lo << shift;

        // Find the part moved from lo to hi.
        // The shift right here can be invalid:
        // for shift == 0 => lshift == half_bits.
        // Split it into 2 valid shifts by (rshift - 1) and 1.
        const auto rshift = half_bits - shift;
        const auto lo_overflow = (x.lo >> (rshift - 1)) >> 1;
        const auto hi = (x.hi << shift) | lo_overflow;
        return {hi, lo};
    }

    // This check is only needed if we want "defined" behavior for shifts
    // larger than size of the Int.
    if (shift < num_bits)
        return {x.lo << (shift - half_bits), 0};

    return 0;
}

template <typename Target>
inline Target narrow_cast(uint64_t x) noexcept
{
    return static_cast<Target>(x);
}

template <typename Target, typename Int>
inline Target narrow_cast(const Int& x) noexcept
{
    return narrow_cast<Target>(x.lo);
}

template <unsigned N>
constexpr uint<N> operator<<(const uint<N>& x, const uint<N>& shift) noexcept
{
    if (shift < num_bits(x))
        return x << narrow_cast<unsigned>(shift);
    return 0;
}

template <unsigned N>
constexpr uint<N> operator>>(const uint<N>& x, unsigned shift) noexcept
{
    constexpr auto half_bits = sizeof(x) * 4;

    if (shift < half_bits)
    {
        auto hi = x.hi >> shift;

        // Find the part moved from hi to lo.
        // To avoid invalid shift left,
        // split them into 2 valid shifts by (lshift - 1) and 1.
        unsigned lshift = half_bits - shift;
        auto hi_overflow = (x.hi << (lshift - 1)) << 1;
        auto lo_part = x.lo >> shift;
        auto lo = lo_part | hi_overflow;
        return {hi, lo};
    }

    if (shift < num_bits(x))
        return {0, x.hi >> (shift - half_bits)};

    return 0;
}

template <unsigned N>
constexpr uint<N> operator>>(const uint<N>& x, const uint<N>& shift) noexcept
{
    if (shift < num_bits(x))
        return x >> narrow_cast<unsigned>(shift);
    return 0;
}

template <unsigned N>
inline uint<N>& operator>>=(uint<N>& x, unsigned shift) noexcept
{
    return x = x >> shift;
}


constexpr uint64_t* as_words(uint128& x) noexcept
{
    return &x.lo;
}

constexpr const uint64_t* as_words(const uint128& x) noexcept
{
    return &x.lo;
}

template <unsigned N>
constexpr uint64_t* as_words(uint<N>& x) noexcept
{
    return as_words(x.lo);
}

template <unsigned N>
constexpr const uint64_t* as_words(const uint<N>& x) noexcept
{
    return as_words(x.lo);
}

/// Implementation of shift left as a loop.
/// This one is slower than the one using "split" strategy.
template <unsigned N>
inline uint<N> shl_loop(const uint<N>& x, unsigned shift)
{
    auto r = uint<N>{};
    constexpr unsigned word_bits = sizeof(uint64_t) * 8;
    constexpr size_t num_words = sizeof(uint<N>) / sizeof(uint64_t);
    auto rw = as_words(r);
    auto words = as_words(x);
    unsigned s = shift % word_bits;
    unsigned skip = shift / word_bits;

    uint64_t carry = 0;
    for (size_t i = 0; i < (num_words - skip); ++i)
    {
        auto w = words[i];
        auto v = (w << s) | carry;
        carry = (w >> (word_bits - s - 1)) >> 1;
        rw[i + skip] = v;
    }
    return r;
}


constexpr std::tuple<uint128, bool> add_with_carry(uint128 a, uint128 b) noexcept
{
    const auto s = a + b;
    const auto k = s < a;
    return {s, k};
}

template <unsigned N>
constexpr std::tuple<uint<N>, bool> add_with_carry(const uint<N>& a, const uint<N>& b) noexcept
{
    uint<N> s;
    bool k1 = false, k2 = false, k3 = false;
    std::tie(s.lo, k1) = add_with_carry(a.lo, b.lo);
    std::tie(s.hi, k2) = add_with_carry(a.hi, b.hi);
    std::tie(s.hi, k3) = add_with_carry(s.hi, typename uint<N>::half_type{k1});
    return {s, k2 || k3};
}

template <unsigned N>
constexpr uint<N> add(const uint<N>& a, const uint<N>& b) noexcept
{
    return std::get<0>(add_with_carry(a, b));
}

template <unsigned N>
inline uint<N> add_loop(const uint<N>& a, const uint<N>& b) noexcept
{
    static constexpr auto num_words = sizeof(a) / sizeof(uint64_t);

    auto x = as_words(a);
    auto y = as_words(b);

    uint<N> s;
    auto z = as_words(s);

    bool k = false;
    for (size_t i = 0; i < num_words; ++i)
    {
        z[i] = x[i] + y[i];
        auto k1 = z[i] < x[i];
        z[i] += k;
        k = (z[i] < k) || k1;
    }

    return s;
}

template <unsigned N>
constexpr uint<N> operator+(const uint<N>& x, const uint<N>& y) noexcept
{
    return add(x, y);
}

template <unsigned N>
constexpr uint<N> operator-(const uint<N>& x) noexcept
{
    return ~x + uint<N>{1};
}

template <unsigned N>
constexpr uint<N> operator-(const uint<N>& x, const uint<N>& y) noexcept
{
    return x + -y;
}

template <typename Int1, typename Int2>
inline Int1& operator+=(Int1& x, const Int2& y)
{
    return x = x + y;
}

template <typename Int1, typename Int2>
inline Int1& operator-=(Int1& x, const Int2& y)
{
    return x = x - y;
}

template <typename Int1, typename Int2>
inline Int1& operator*=(Int1& x, const Int2& y)
{
    return x = x * y;
}

template <typename Int>
constexpr typename traits<Int>::double_type umul(const Int& x, const Int& y) noexcept
{
    auto t0 = umul(x.lo, y.lo);
    auto t1 = umul(x.hi, y.lo);
    auto t2 = umul(x.lo, y.hi);
    auto t3 = umul(x.hi, y.hi);

    auto u1 = t1 + t0.hi;
    auto u2 = t2 + u1.lo;

    auto lo = (u2 << (num_bits(x) / 2)) | t0.lo;
    auto hi = t3 + u2.hi + u1.hi;

    return {hi, lo};
}

template <typename Int>
inline Int mul(const Int& a, const Int& b) noexcept
{
    // Requires 1 full mul, 2 muls and 2 adds.
    // Clang & GCC implements 128-bit multiplication this way.

    auto t = umul(a.lo, b.lo);
    auto hi = (a.lo * b.hi) + (a.hi * b.lo) + hi_half(t);
    auto lo = lo_half(t);

    return {hi, lo};
}

template <typename Int>
inline typename traits<Int>::double_type umul_loop(const Int& x, const Int& y) noexcept
{
    constexpr int num_words = sizeof(Int) / sizeof(uint64_t);

    typename traits<Int>::double_type p;
    auto pw = as_words(p);
    auto uw = as_words(x);
    auto vw = as_words(y);

    for (int j = 0; j < num_words; ++j)
    {
        uint64_t k = 0;
        for (int i = 0; i < num_words; ++i)
        {
            auto t = umul(uw[i], vw[j]) + pw[i + j] + k;
            pw[i + j] = t.lo;
            k = t.hi;
        }
        pw[j + num_words] = k;
    }
    return p;
}

template <typename Int>
inline Int mul_loop_opt(const Int& u, const Int& v) noexcept
{
    constexpr int num_words = sizeof(Int) / sizeof(uint64_t);

    Int p;
    auto pw = as_words(p);
    auto uw = as_words(u);
    auto vw = as_words(v);

    for (int j = 0; j < num_words; j++)
    {
        uint64_t k = 0;
        for (int i = 0; i < (num_words - j - 1); i++)
        {
            auto t = umul(uw[i], vw[j]) + pw[i + j] + k;
            pw[i + j] = t.lo;
            k = t.hi;
        }
        pw[num_words - 1] += uw[num_words - j - 1] * vw[j] + k;
    }
    return p;
}

inline uint256 operator*(const uint256& x, const uint256& y) noexcept
{
    return mul(x, y);
}

template <unsigned N>
inline uint<N> operator*(const uint<N>& x, const uint<N>& y) noexcept
{
    return mul_loop_opt(x, y);
}

inline uint256& operator*=(uint256& x, const uint256& y) noexcept
{
    return x = x * y;
}

inline uint512& operator*=(uint512& x, const uint512& y) noexcept
{
    return x = x * y;
}

template <unsigned N>
constexpr uint<N> exp(uint<N> base, uint<N> exponent) noexcept
{
    auto result = uint<N>{1};
    while (exponent != 0)
    {
        if ((exponent & 1) != 0)
            result *= base;
        base *= base;
        exponent >>= 1;
    }
    return result;
}

template <unsigned N>
constexpr unsigned clz(const uint<N>& x) noexcept
{
    unsigned half_bits = num_bits(x) / 2;

    // TODO: Try:
    // bool take_hi = h != 0;
    // bool take_lo = !take_hi;
    // unsigned clz_hi = take_hi * clz(h);
    // unsigned clz_lo = take_lo * (clz(l) | half_bits);
    // return clz_hi | clz_lo;

    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    // FIXME: For `x == 0` this is UB.
    return x.hi == 0 ? clz(x.lo) | half_bits : clz(x.hi);
}

template <typename Word, typename Int>
std::array<Word, sizeof(Int) / sizeof(Word)> to_words(Int x) noexcept
{
    std::array<Word, sizeof(Int) / sizeof(Word)> words;
    std::memcpy(&words, &x, sizeof(x));
    return words;
}

template <typename Word>
unsigned count_significant_words_loop(uint256 x) noexcept
{
    auto words = to_words<Word>(x);
    for (size_t i = words.size(); i > 0; --i)
    {
        if (words[i - 1] != 0)
            return static_cast<unsigned>(i);
    }
    return 0;
}

template <typename Word, typename Int>
inline typename std::enable_if<sizeof(Word) == sizeof(Int), unsigned>::type count_significant_words(
    const Int& x) noexcept
{
    return x != 0 ? 1 : 0;
}

template <typename Word, typename Int>
inline typename std::enable_if<sizeof(Word) < sizeof(Int), unsigned>::type count_significant_words(
    const Int& x) noexcept
{
    constexpr auto num_words = static_cast<unsigned>(sizeof(x) / sizeof(Word));
    auto h = count_significant_words<Word>(hi_half(x));
    auto l = count_significant_words<Word>(lo_half(x));
    return h != 0 ? h + (num_words / 2) : l;
}

div_result<uint256> udiv_qr_knuth_hd_base(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_llvm_base(const uint256& u, const uint256& v);
div_result<uint256> udiv_qr_knuth_opt_base(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_opt(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_64(const uint256& x, const uint256& y);
div_result<uint512> udiv_qr_knuth_512(const uint512& x, const uint512& y);
div_result<uint512> udiv_qr_knuth_512_64(const uint512& x, const uint512& y);

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept;
div_result<uint512> udivrem(const uint512& x, const uint512& y) noexcept;

template <unsigned N>
constexpr div_result<uint<N>> sdivrem(const uint<N>& u, const uint<N>& v) noexcept
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
constexpr uint<N> operator/(const uint<N>& x, const uint<N>& y) noexcept
{
    return udivrem(x, y).quot;
}

template <unsigned N>
constexpr uint<N> operator%(const uint<N>& x, const uint<N>& y) noexcept
{
    return udivrem(x, y).rem;
}

template <unsigned N>
inline std::string to_string(uint<N> x)
{
    if (x == 0)
        return "0";

    std::string s;
    while (x != 0)
    {
        const auto res = udivrem(x, 10);
        x = res.quot;
        const auto c = static_cast<size_t>(res.rem);
        s.push_back(static_cast<char>('0' + c));
    }
    std::reverse(s.begin(), s.end());
    return s;
}

inline std::string to_string(uint128 x)
{
    return to_string(uint256(x));
}

template <typename Int>
inline Int from_string(const std::string& s)
{
    Int x{};

    for (auto c : s)
    {
        auto v = c - '0';
        x *= 10;
        x += v;
    }
    return x;
}

template <unsigned N>
inline uint<N> bswap(const uint<N>& x) noexcept
{
    return {bswap(x.lo), bswap(x.hi)};
}


template <typename Int>
inline Int parse_literal(const char* s) noexcept
{
    // TODO: It can buffer overflow.
    // TODO: Control the length of the s, not to overflow the integer.
    Int x;

    if (s[0] == '0' && s[1] == 'x')
    {
        s += 2;
        while (auto c = *s++)
        {
            x *= 16;
            if (c <= '9')
                x += (c - '0');
            else
                x += (c - 'a' + 10);
        }
        return x;
    }

    while (auto c = *s++)
    {
        x *= 10;
        x += (c - '0');
    }
    return x;
}

inline uint256 operator"" _u256(const char* s) noexcept
{
    return parse_literal<uint256>(s);
}

inline uint512 operator"" _u512(const char* s) noexcept
{
    return parse_literal<uint512>(s);
}


// Support for type conversions for binary operators.

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator+(const uint<N>& x, const T& y) noexcept
{
    return x + uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator+(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) + y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator-(const uint<N>& x, const T& y) noexcept
{
    return x - uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator-(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) - y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator*(const uint<N>& x, const T& y) noexcept
{
    return x * uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator*(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) * y;
}


template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator|(const uint<N>& x, const T& y) noexcept
{
    return x | uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator|(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) | y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator&(const uint<N>& x, const T& y) noexcept
{
    return x & uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator&(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) & y;
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator^(const uint<N>& x, const T& y) noexcept
{
    return x ^ uint<N>(y);
}

template <unsigned N, typename T,
    typename = typename std::enable_if<std::is_convertible<T, uint<N>>::value>::type>
constexpr uint<N> operator^(const T& x, const uint<N>& y) noexcept
{
    return uint<N>(x) ^ y;
}


namespace be  // Conversions to/from BE bytes.
{
inline intx::uint256 uint256(const uint8_t bytes[32]) noexcept
{
    intx::uint256 x;
    std::memcpy(&x, bytes, sizeof(x));
    return bswap(x);
}

template <typename Int>
inline void store(uint8_t* dst, const Int& x) noexcept
{
    auto d = bswap(x);
    std::memcpy(dst, &d, sizeof(d));
}

}  // namespace be

}  // namespace intx
