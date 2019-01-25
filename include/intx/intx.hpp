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

namespace intx
{
inline std::tuple<uint32_t, uint32_t> udivrem_long_asm(uint64_t u, uint32_t v)
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint32_t q, r;
    uint32_t uh = static_cast<uint32_t>(u >> 32);
    uint32_t ul = static_cast<uint32_t>(u);
    asm("divl %4" : "=d"(r), "=a"(q) : "d"(uh), "a"(ul), "g"(v));
    return std::make_tuple(q, r);
}

inline std::tuple<uint32_t, uint32_t> udivrem_long(uint64_t u, uint32_t v)
{
    auto q = static_cast<uint32_t>(u / v);
    auto r = static_cast<uint32_t>(u % v);
    return std::make_tuple(q, r);
}

struct uint256
{
    constexpr uint256(uint64_t x = 0) noexcept : lo(x) {}
    constexpr uint256(uint128 lo) noexcept : lo(lo) {}
    constexpr uint256(uint128 lo, uint128 hi) noexcept : lo(lo), hi(hi) {}

    uint128 lo = 0;
    uint128 hi = 0;

    /// Explicit converting operator for all builtin integral types.
    template <typename Int, typename = typename std::enable_if<std::is_integral<Int>::value>::type>
    explicit operator Int() const noexcept
    {
        return static_cast<Int>(lo.lo);
    }
};

struct uint512
{
    constexpr uint512(uint64_t x = 0) noexcept : lo(x) {}
    constexpr uint512(uint256 lo) noexcept : lo(lo) {}
    constexpr uint512(uint256 lo, uint256 hi) noexcept : lo(lo), hi(hi) {}

    uint256 lo = {};
    uint256 hi = {};
};


template <typename T>
struct traits
{
};

template <>
struct traits<uint64_t>
{
    using double_type = uint128;
    using half_type = uint32_t;

    static constexpr unsigned bits = 64;
    static constexpr unsigned half_bits = 32;
    static constexpr int unr_iterations = 6;
};

template <>
struct traits<uint128>
{
    using double_type = uint256;
    using half_type = uint64_t;

    static constexpr unsigned bits = 128;
    static constexpr unsigned half_bits = 64;
    static constexpr int unr_iterations = 7;
};

template <>
struct traits<uint256>
{
    using double_type = uint512;
    using half_type = uint128;

    static constexpr unsigned bits = 256;
    static constexpr unsigned half_bits = 128;
    static constexpr int unr_iterations = 8;
};

template <>
struct traits<uint512>
{
    //    using double_type = uint1024;
    using half_type = uint256;

    static constexpr unsigned bits = 512;
    static constexpr unsigned half_bits = 256;
    //    static constexpr int unr_iterations = 8;
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

constexpr uint128 join(uint64_t hi, uint64_t lo)
{
    return (uint128(hi) << 64) | lo;
}

constexpr uint256 join(uint128 hi, uint128 lo)
{
    return uint256{lo, hi};
}

template <typename T>
constexpr unsigned num_bits(const T&)
{
    return sizeof(T) * 8;
}

template <typename Int>
inline bool operator==(Int a, Int b)
{
    auto a_lo = lo_half(a);
    auto a_hi = hi_half(a);
    auto b_lo = lo_half(b);
    auto b_hi = hi_half(b);
    return (a_lo == b_lo) & (a_hi == b_hi);
}

template <typename Int>
inline bool operator==(Int a, uint64_t b)
{
    return a == Int(b);
}

inline bool operator!=(uint256 a, uint256 b)
{
    return !(a == b);
}

inline bool operator!=(uint512 a, uint512 b)
{
    return !(a == b);
}

template <typename Int>
inline bool operator<(Int a, Int b)
{
    auto a_lo = lo_half(a);
    auto a_hi = hi_half(a);
    auto b_lo = lo_half(b);
    auto b_hi = hi_half(b);
    // Bitwise operators are used to implement logic here to avoid branching.
    // It also should make the function smaller, but no proper benchmark has
    // been done.
    return (a_hi < b_hi) | ((a_hi == b_hi) & (a_lo < b_lo));
}

template <typename Int>
inline bool operator<(Int a, uint64_t b)
{
    return a < Int(b);
}

template <typename Int>
inline bool operator<(uint64_t a, Int b)
{
    return Int(a) < b;
}

inline bool operator>=(uint256 a, uint256 b)
{
    return !(a < b);
}

template <typename Int>
inline bool operator<=(Int a, Int b)
{
    return (a < b) || (a == b);
}

template <typename Int>
inline constexpr Int operator|(const Int& x, const Int& y) noexcept
{
    return {x.lo | y.lo, x.hi | y.hi};
}

template <typename Int>
inline constexpr Int operator&(const Int& x, const Int& y) noexcept
{
    return {x.lo & y.lo, x.hi & y.hi};
}

template <typename Int>
inline constexpr Int operator^(const Int& x, const Int& y) noexcept
{
    return {x.lo ^ y.lo, x.hi ^ y.hi};
}

template <typename Int>
inline constexpr Int operator~(const Int& x) noexcept
{
    return {~x.lo, ~x.hi};
}

inline uint128 shl(uint128 a, unsigned b)
{
    return a << b;
}

inline uint64_t shl(uint64_t a, unsigned b)
{
    return a << b;
}

inline uint128 lsr(uint128 a, unsigned b)
{
    return a >> b;
}

template <typename Int>
inline Int shl(Int x, unsigned shift) noexcept
{
    using half_type = typename traits<Int>::half_type;
    constexpr auto bits = traits<Int>::bits;
    constexpr auto half_bits = traits<Int>::half_bits;

    if (shift < half_bits)
    {
        half_type lo = shl(x.lo, shift);

        // Find the part moved from lo to hi.
        // The shift right here can be invalid:
        // for shift == 0 => lshift == half_bits.
        // Split it into 2 valid shifts by (rshift - 1) and 1.
        unsigned rshift = half_bits - shift;
        half_type lo_overflow = lsr(lsr(x.lo, rshift - 1), 1);
        half_type hi_part = shl(x.hi, shift);
        half_type hi = hi_part | lo_overflow;
        return Int{lo, hi};
    }

    // This check is only needed if we want "defined" behavior for shifts
    // larger than size of the Int.
    if (shift < bits)
    {
        half_type hi = shl(x.lo, shift - half_bits);
        return Int{0, hi};
    }

    return 0;
}

template <typename Int>
inline Int operator<<(const Int& x, unsigned shift) noexcept
{
    return shl(x, shift);
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

template <typename Int>
inline Int operator<<(const Int& x, const Int& shift) noexcept
{
    if (shift < traits<Int>::bits)
        return x << narrow_cast<unsigned>(shift);
    return 0;
}

template <typename Int>
inline Int operator>>(const Int& x, const Int& shift) noexcept
{
    if (shift < traits<Int>::bits)
        return lsr(x, narrow_cast<unsigned>(shift));
    return 0;
}

template <typename Int>
inline Int& operator>>=(Int& x, unsigned shift) noexcept
{
    return x = lsr(x, shift);
}

template <typename Int>
inline Int lsr(Int x, unsigned shift)
{
    using half_type = typename traits<Int>::half_type;
    constexpr auto bits = traits<Int>::bits;
    constexpr auto half_bits = traits<Int>::half_bits;

    if (shift < half_bits)
    {
        half_type hi = lsr(x.hi, shift);

        // Find the part moved from hi to lo.
        // To avoid invalid shift left,
        // split them into 2 valid shifts by (lshift - 1) and 1.
        unsigned lshift = half_bits - shift;
        half_type hi_overflow = shl(shl(x.hi, lshift - 1), 1);
        half_type lo_part = lsr(x.lo, shift);
        half_type lo = lo_part | hi_overflow;
        return Int{lo, hi};
    }

    if (shift < bits)
    {
        auto lo = lsr(x.hi, shift - half_bits);
        return Int{lo, 0};
    }

    return 0;
}

template <typename Int>
inline std::array<uint64_t, sizeof(Int) / sizeof(uint64_t)>& as_words(Int& x)
{
    return reinterpret_cast<std::array<uint64_t, sizeof(Int) / sizeof(uint64_t)>&>(x);
}

/// Implementation of shift left as a loop.
/// This one is slower than the one using "split" strategy.
template <typename Int>
inline Int shl_loop(Int x, unsigned shift)
{
    Int r;
    constexpr unsigned word_bits = sizeof(uint64_t) * 8;
    auto& rw = as_words(r);
    const auto& words = as_words(x);
    unsigned s = shift % word_bits;
    unsigned skip = shift / word_bits;

    uint64_t carry = 0;
    for (size_t i = 0; i < (words.size() - skip); ++i)
    {
        auto w = words[i];
        auto v = (w << s) | carry;
        carry = (w >> (word_bits - s - 1)) >> 1;
        rw[i + skip] = v;
    }
    return r;
}


inline std::tuple<uint128, bool> add_with_carry(uint128 a, uint128 b)
{
    auto s = a + b;
    auto k = s < a;
    return std::make_tuple(s, k);
}

inline std::tuple<uint256, bool> add_with_carry(uint256 a, uint256 b)
{
    uint256 s;
    bool k1, k2, k3;
    std::tie(s.lo, k1) = add_with_carry(a.lo, b.lo);
    std::tie(s.hi, k2) = add_with_carry(a.hi, b.hi);
    std::tie(s.hi, k3) = add_with_carry(s.hi, static_cast<uint128>(k1));
    return std::make_tuple(s, k2 || k3);
}

inline std::tuple<uint512, bool> add_with_carry(uint512 a, uint512 b)
{
    uint512 s;
    bool k1, k2, k3;
    std::tie(s.lo, k1) = add_with_carry(a.lo, b.lo);
    std::tie(s.hi, k2) = add_with_carry(a.hi, b.hi);
    std::tie(s.hi, k3) = add_with_carry(s.hi, static_cast<uint256>(k1));
    return std::make_tuple(s, k2 || k3);
}

template <typename Int>
inline Int add(Int a, Int b)
{
    return std::get<0>(add_with_carry(a, b));
}

template <typename Int, typename Int2>
inline Int add(Int a, Int2 b)
{
    return add(a, Int(b));
}

template <typename Int>
inline constexpr Int operator-(const Int& x) noexcept
{
    return add(~x, uint64_t(1));
}

inline uint128 sub(uint128 a, uint128 b)
{
    return a - b;
}

template <typename Int>
inline Int sub(Int a, Int b)
{
    return add(a, -b);
}

inline uint128 mul(const uint128& a, const uint128& b)
{
    return a * b;
}

inline uint64_t mul(uint64_t a, uint64_t b)
{
    return a * b;
}

inline uint128 add(uint128 a, uint128 b)
{
    return a + b;
}

inline uint64_t add(uint64_t a, uint64_t b)
{
    return a + b;
}

inline uint128 bitwise_or(uint128 a, uint128 b)
{
    return a | b;
}

inline uint128 umul_full(uint64_t a, uint64_t b)
{
    return uint128(a) * uint128(b);
}

template <typename Int>
inline Int operator+(Int x, Int y)
{
    return add(x, y);
}

template <typename Int>
inline Int operator+(Int x, uint64_t y)
{
    return add(x, Int(y));
}

template <typename Int1, typename Int2>
inline decltype(sub(Int1{}, Int2{})) operator-(const Int1& x, const Int2& y)
{
    return sub(x, y);
}

inline uint256 operator<<(uint256 x, unsigned y) noexcept
{
    return shl(x, y);
}

inline uint256 operator>>(uint256 x, unsigned y)
{
    return lsr(x, y);
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
typename traits<Int>::double_type umul_full(const Int& a, const Int& b) noexcept
{
    // Hacker's Delight version.

    Int al = lo_half(a);
    Int ah = hi_half(a);
    Int bl = lo_half(b);
    Int bh = hi_half(b);

    Int t, l, h, u;

    t = mul(al, bl);
    l = lo_half(t);
    h = hi_half(t);
    t = mul(ah, bl);
    t = add(t, h);
    h = hi_half(t);

    u = mul(al, bh);
    t = add(u, Int(lo_half(t)));
    u = shl(t, traits<Int>::half_bits);
    l = l | u;
    u = mul(ah, bh);
    t = add(u, Int(hi_half(t)));
    h = add(h, t);

    return {l, h};
}

template <typename Int>
inline Int mul(const Int& a, const Int& b) noexcept
{
    // Requires 1 full mul, 2 muls and 2 adds.
    // Clang & GCC implements 128-bit multiplication this way.

    auto t = umul_full(a.lo, b.lo);
    auto hi = (a.lo * b.hi) + (a.hi * b.lo) + hi_half(t);
    auto lo = lo_half(t);

    return {lo, hi};
}

inline uint256 mul2(uint256 u, uint256 v)
{
    auto u1 = hi_half(u);
    auto u0 = lo_half(u);
    auto v1 = hi_half(v);
    auto v0 = lo_half(v);

    auto m2 = umul_full(u1, v1);
    auto m1 = umul_full(u1 - u0, v0 - v1);
    auto m0 = umul_full(u0, v0);

    auto t4 = m2 << 128;
    auto t3 = m2 << 64;
    auto t2 = m1 << 64;
    auto t1 = m0 << 64;
    auto t0 = m0;

    return t4 + t3 + t2 + t1 + t0;
}

inline uint512 umul_full_loop(const uint256& u, const uint256& v) noexcept
{
    uint512 p;
    auto pw = reinterpret_cast<uint64_t*>(&p);
    auto uw = reinterpret_cast<const uint64_t*>(&u);
    auto vw = reinterpret_cast<const uint64_t*>(&v);

    for (int j = 0; j < 4; j++)
    {
        uint64_t k = 0;
        for (int i = 0; i < 4; i++)
        {
            uint128 t = uint128(uw[i]) * vw[j] + pw[i + j] + k;
            pw[i + j] = lo_half(t);
            k = hi_half(t);
        }
        pw[j + 4] = k;
    }
    return p;
}

inline uint256 mul_loop(const uint256& u, const uint256& v) noexcept
{
    return umul_full_loop(u, v).lo;
}

inline uint256 mul_loop_opt(const uint256& u, const uint256& v) noexcept
{
    uint256 p;
    auto pw = reinterpret_cast<uint64_t*>(&p);
    auto uw = reinterpret_cast<const uint64_t*>(&u);
    auto vw = reinterpret_cast<const uint64_t*>(&v);

    for (int j = 0; j < 4; j++)
    {
        uint64_t k = 0;
        for (int i = 0; i < (4 - j); i++)
        {
            uint128 t = uint128(uw[i]) * vw[j] + pw[i + j] + k;
            pw[i + j] = lo_half(t);
            k = hi_half(t);
        }
    }
    return p;
}

template <typename Int>
inline Int umul_hi(Int a, Int b)
{
    return hi_half(umul_full(a, b));
}

inline uint256 operator*(uint256 x, uint256 y)
{
    return mul(x, y);
}

inline uint512 operator*(uint512 x, uint512 y)
{
    return mul(x, y);
}

inline uint256& operator*=(uint256& x, uint256 y)
{
    return x = x * y;
}

inline uint512& operator*=(uint512& x, uint512 y)
{
    return x = x * y;
}

template <typename Int>
Int exp(Int base, Int exponent) noexcept
{
    Int result{1};
    while (exponent != 0)
    {
        if ((exponent & Int{1}) != 0)
            result *= base;
        base *= base;
        exponent >>= 1;
    }
    return result;
}

template <typename Int>
inline unsigned clz(Int x)
{
    auto l = lo_half(x);
    auto h = hi_half(x);
    unsigned half_bits = num_bits(x) / 2;

    // TODO: Try:
    // bool take_hi = h != 0;
    // bool take_lo = !take_hi;
    // unsigned clz_hi = take_hi * clz(h);
    // unsigned clz_lo = take_lo * (clz(l) | half_bits);
    // return clz_hi | clz_lo;

    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    // FIXME: For `x == 0` this is UB.
    return h == 0 ? clz(l) | half_bits : clz(h);
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
inline unsigned count_significant_words(const Int& x) noexcept
{
    constexpr auto num_words = static_cast<unsigned>(sizeof(x) / sizeof(Word));
    auto h = count_significant_words<Word>(hi_half(x));
    auto l = count_significant_words<Word>(lo_half(x));
    return h != 0 ? h + (num_words / 2) : l;
}

template <>
inline unsigned count_significant_words<uint8_t, uint8_t>(const uint8_t& x) noexcept
{
    return x != 0 ? 1 : 0;
}

template <>
inline unsigned count_significant_words<uint32_t, uint32_t>(const uint32_t& x) noexcept
{
    return x != 0 ? 1 : 0;
}

template <>
inline unsigned count_significant_words<uint64_t, uint64_t>(const uint64_t& x) noexcept
{
    return x != 0 ? 1 : 0;
}

template <typename Int>
inline div_result<Int> udivrem_unr(const Int& x, const Int& y) noexcept
{
    // decent start
    unsigned c = clz(y);
    auto z = shl(Int(1), c);

    // z recurrence
    auto my = -y;
    for (int i = 0; i < traits<Int>::unr_iterations; ++i)
    {
        auto m = mul(my, z);
        auto zd = umul_hi(z, m);
        //        if (zd == 0)
        //            break;
        z = add(z, zd);
    }

    // q estimate
    auto q = umul_hi(x, z);
    auto r = sub(x, mul(y, q));

    // q refinement
    if (r >= y)
    {
        r = sub(r, y);
        q = add(q, 1);
        if (r >= y)
        {
            r = sub(r, y);
            q = add(q, 1);
        }
    }
    return {q, r};
}

div_result<uint256> udiv_qr_knuth_hd_base(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_llvm_base(const uint256& u, const uint256& v);
div_result<uint256> udiv_qr_knuth_opt_base(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_opt(const uint256& x, const uint256& y);
div_result<uint256> udiv_qr_knuth_64(const uint256& x, const uint256& y);
div_result<uint512> udiv_qr_knuth_512(const uint512& x, const uint512& y);
div_result<uint512> udiv_qr_knuth_512_64(const uint512& x, const uint512& y);

template <typename Int>
inline std::tuple<Int, Int> udiv_long(typename traits<Int>::double_type u, Int v)
{
    using tr = traits<Int>;

    constexpr Int b = Int(1) << (tr::bits / 2);

    unsigned s = clz(v);
    v <<= s;
    Int vn1 = hi_half(v);
    Int vn0 = lo_half(v);

    // TODO: Check out this way of shifting by 0:
    // un32 = (u1 << s) | ((u0 >> (64 - s)) & (-s >> 31));

    u = u << s;
    Int un32 = hi_half(u);
    Int un10 = lo_half(u);

    auto un1 = hi_half(un10);
    auto un0 = lo_half(un10);
    using half_type = decltype(un0);

    Int q1 = un32 / vn1;
    Int rhat = un32 % vn1;

again1:
    if (q1 >= b || q1 * vn0 > join(static_cast<half_type>(rhat), un1))
    {
        q1 = q1 - 1;
        rhat = rhat + vn1;
        if (rhat < b)
            goto again1;
    }

    Int un21 = join(static_cast<half_type>(un32), un1) - q1 * v;

    Int q0 = un21 / vn1;
    rhat = un21 % vn1;

again2:
    if (q0 >= b || q0 * vn0 > join(static_cast<half_type>(rhat), un0))
    {
        q0 = q0 - 1;
        rhat = rhat + vn1;
        if (rhat < b)
            goto again2;
    }

    Int r = (un21 * b + un0 - q0 * v) >> s;
    Int q = q1 * b + q0;

    return std::make_tuple(q, r);
}

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept;
div_result<uint512> udivrem(const uint512& x, const uint512& y) noexcept;

template <typename Int>
div_result<Int> sdivrem(const Int& u, const Int& v) noexcept
{
    const auto sign_mask = Int(1) << (sizeof(Int) * 8 - 1);
    auto u_is_neg = (u & sign_mask) != 0;
    auto v_is_neg = (v & sign_mask) != 0;

    auto u_abs = u_is_neg ? -u : u;
    auto v_abs = v_is_neg ? -v : v;

    auto q_is_neg = u_is_neg ^ v_is_neg;

    auto res = udivrem(u_abs, v_abs);

    return {q_is_neg ? -res.quot : res.quot, u_is_neg ? -res.rem : res.rem};
}

template <typename Int>
inline Int operator/(const Int& x, const Int& y) noexcept
{
    return udivrem(x, y).quot;
}

template <typename Int>
inline Int operator%(const Int& x, const Int& y) noexcept
{
    return udivrem(x, y).rem;
}

inline std::string to_string(uint256 x)
{
    if (x == 0)
        return "0";

    std::string s;
    while (x != 0)
    {
        const auto res = udivrem_unr(x, uint256(10));
        x = res.quot;
        auto c = static_cast<size_t>(res.rem);
        s.push_back(static_cast<char>('0' + c));
    }
    std::reverse(s.begin(), s.end());
    return s;
}

inline std::string to_string(uint128 x)
{
    return to_string(uint256(x));
}

inline std::string to_string(uint512 x)
{
    if (x == 0)
        return "0";

    std::string s;
    while (x != 0)
    {
        const auto res = udiv_qr_knuth_512(x, uint512(10));
        x = res.quot;
        auto c = static_cast<size_t>(res.rem.lo);
        s.push_back(static_cast<char>('0' + c));
    }
    std::reverse(s.begin(), s.end());
    return s;
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

constexpr uint64_t bswap(uint64_t x) noexcept
{
    return __builtin_bswap64(x);
}

constexpr uint128 bswap(uint128 x) noexcept
{
    return {bswap(x.lo), bswap(x.hi)};
}

template <typename Int>
inline Int bswap(const Int& x) noexcept
{
    return {bswap(x.hi), bswap(x.lo)};
}


// constexpr inline uint256 operator"" _u256(unsigned long long x) noexcept
//{
//    return uint256{x};
//}

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
