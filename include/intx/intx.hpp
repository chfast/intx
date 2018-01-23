// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <limits>
#include <tuple>

namespace intx
{
namespace generic
{
struct uint128
{
    uint64_t lo = 0;
    uint64_t hi = 0;
};


inline unsigned clz(uint64_t a)
{
    unsigned c = 0;
    for (; c < 64; ++c)
    {
        if ((a & 0x8000000000000000) != 0)
            break;
        a <<= 1;
    }
    return c;
}
}

namespace gcc
{
using uint128 = unsigned __int128;

inline unsigned clz(uint64_t a)
{
    return __builtin_clzl(a);
}

inline unsigned clz(unsigned x)
{
    return __builtin_clz(x);
}

inline std::tuple<uint64_t, uint64_t> udivrem_long(uint128 u, uint64_t v)
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    uint64_t uh = static_cast<uint64_t>(u >> 64);
    uint64_t ul = static_cast<uint64_t>(u);
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(uh), "a"(ul), "g"(v));
    return std::make_tuple(q, r);
}

inline std::tuple<uint32_t, uint32_t> udivrem_long(uint64_t u, uint32_t v)
{
    auto q = static_cast<uint32_t>(u / v);
    auto r = static_cast<uint32_t>(u % v);
    return std::make_tuple(q, r);
}
}

using namespace gcc;


struct uint256
{
    constexpr uint256(uint128 lo = 0, uint128 hi = 0) : lo(lo), hi(hi) {}

    uint128 lo = 0;
    uint128 hi = 0;

    explicit operator unsigned() const
    {
        return static_cast<unsigned>(lo);
    }

    explicit operator unsigned long() const
    {
        return static_cast<unsigned long>(lo);
    }
};

struct uint512
{
    constexpr uint512(uint128 lo) : lo(lo) {}
    constexpr uint512(uint256 lo = 0, uint256 hi = 0) : lo(lo), hi(hi) {}

    uint256 lo = 0;
    uint256 hi = 0;
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

constexpr uint32_t lo_half(uint64_t x)
{
    return static_cast<uint32_t>(x);
}

constexpr uint32_t hi_half(uint64_t x)
{
    return static_cast<uint32_t>(x >> 32);
}

constexpr uint64_t lo_half(uint128 x)
{
    return static_cast<uint64_t>(x);
}

constexpr uint64_t hi_half(uint128 x)
{
    return static_cast<uint64_t>(x >> 64);
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

template<typename Int>
inline bool operator==(Int a, Int b)
{
    auto a_lo = lo_half(a);
    auto a_hi = hi_half(a);
    auto b_lo = lo_half(b);
    auto b_hi = hi_half(b);
    return (a_lo == b_lo) & (a_hi == b_hi);
}

template<typename Int>
inline bool operator==(Int a, uint64_t b)
{
    return a == Int(b);
}

inline bool operator!=(uint256 a, uint256 b)
{
    return !(a == b);
}

template<typename Int>
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

template<typename Int>
inline bool operator<(Int a, uint64_t b)
{
    return a < Int(b);
}

inline bool operator>=(uint256 a, uint256 b)
{
    return !(a < b);
}

template<typename Int>
inline bool operator<=(Int a, Int b)
{
    return (a < b) || (a == b);
}


inline constexpr uint256 bitwise_or(uint256 x, uint256 y)
{
    return {x.lo | y.lo, x.hi | y.hi};
}

inline constexpr uint256 bitwise_and(uint256 x, uint256 y)
{
    return {x.lo & y.lo, x.hi & y.hi};
}

inline constexpr uint256 bitwise_xor(uint256 x, uint256 y)
{
    return {x.lo ^ y.lo, x.hi ^ y.hi};
}

inline constexpr uint256 bitwise_not(uint256 x)
{
    return {~x.lo, ~x.hi};
}

inline uint256 shl(uint256 x, uint256 shift)
{
    using Int = uint256;

    if (shift == 0)
        return x;

    constexpr auto bits = traits<Int>::bits;
    constexpr auto half_bits = traits<Int>::half_bits;

    if (shift < half_bits)
    {
        auto lo = x.lo << shift.lo;
        auto lo_overflow = x.lo >> (half_bits - shift.lo);
        auto hi_part = x.hi << shift.lo;
        auto hi = hi_part | lo_overflow;
        return {lo, hi};
    }

    if (shift < bits)
    {
        auto hi = x.lo << (shift.lo - half_bits);
        return {0, hi};
    }

    return 0;
}

inline uint256 lsr(uint256 x, uint256 shift)
{
    if (shift == 0)
        return x;

    if (shift < 128)
    {
        auto hi = x.hi >> shift.lo;
        auto hi_overflow = x.hi << (128 - shift.lo);
        auto lo_part = x.lo >> shift.lo;
        auto lo = lo_part | hi_overflow;
        return {lo, hi};
    }

    if (shift < 256)
    {
        auto lo = x.hi >> (shift.lo - 128);
        return {lo, 0};
    }

    return 0;
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

template<typename Int>
inline Int add(Int a, Int b)
{
    return std::get<0>(add_with_carry(a, b));
}

template<typename Int, typename Int2>
inline Int add(Int a, Int2 b)
{
    return add(a, Int(b));
}

inline uint128 minus(uint128 x)
{
    return -x;
}

inline uint64_t minus(uint64_t x)
{
    return -x;
}

inline uint256 minus(uint256 x)
{
    return add(bitwise_not(x), uint64_t(1));
}

inline uint128 sub(uint128 a, uint128 b)
{
    return a - b;
}

inline uint256 sub(uint256 a, uint256 b)
{
    return add(a, minus(b));
}

inline uint128 mul(uint128 a, uint128 b)
{
    return a * b;
}

inline uint64_t mul(uint64_t a, uint64_t b)
{
    return a * b;
}

inline std::tuple<uint128, uint128> udiv_qr(uint128 a, uint128 b)
{
    return std::make_tuple(a / b, a % b);
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

inline uint128 shl(uint128 a, uint128 b)
{
    return a << b;
}

inline uint64_t shl(uint64_t a, uint64_t b)
{
    return a << b;
}

inline uint128 umul_full(uint64_t a, uint64_t b)
{
    return uint128(a) * uint128(b);
}

template<typename Int>
inline Int operator+(Int x, Int y)
{
    return add(x, y);
}

template<typename Int>
inline Int operator+(Int x, uint64_t y)
{
    return add(x, Int(y));
}

inline uint256 operator-(uint256 x, uint256 y)
{
    return sub(x, y);
}

inline uint256 operator<<(uint256 x, uint256 y)
{
    return shl(x, y);
}

inline uint256 operator>>(uint256 x, uint256 y)
{
    return lsr(x, y);
}

inline uint256& operator+=(uint256& x, uint256 y)
{
    return x = x + y;
}


template <typename Int>
typename traits<Int>::double_type umul_full(Int a, Int b)
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
    l = bitwise_or(l, u);
    u = mul(ah, bh);
    t = add(u, Int(hi_half(t)));
    h = add(h, t);

    return {l, h};
}

template<typename Int>
inline Int mul(Int a, Int b)
{
    auto t = umul_full(a.lo, b.lo);
    auto l = lo_half(t);
    auto u = hi_half(t);
    t = umul_full(a.hi, b.lo);
    t = t + Int(u);

    u = lo_half(t);
    t = umul_full(a.lo, b.hi);
    t = t + Int(u);

    auto h = lo_half(t);

    return {l, h};
}

inline uint512 mul512(uint512 a, uint512 b)
{
    return mul(a, b);
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

using gcc::clz;

template <typename Int>
inline unsigned clz(Int x)
{
    auto l = lo_half(x);
    auto h = hi_half(x);
    unsigned half_bits = num_bits(x) / 2;

    // In this order `h == 0` we get less instructions than in case of `h != 0`.
    // FIXME: For `x == 0` this is UB.
    return h == 0 ? clz(l) + half_bits : clz(h);
}

template<typename Word, typename Int>
std::array<Word, sizeof(Int) / sizeof(Word)> to_words(Int x) noexcept
{
    std::array<Word, sizeof(Int) / sizeof(Word)> words;
    std::memcpy(&words, &x, sizeof(x));
    return words;
}

template<typename Word>
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

template<typename Word, typename Int>
inline unsigned count_significant_words(Int x) noexcept
{
    constexpr auto num_words = static_cast<unsigned>(sizeof(x) / sizeof(Word));
    auto h = count_significant_words<Word>(hi_half(x));
    auto l = count_significant_words<Word>(lo_half(x));
    return h != 0 ? h + (num_words / 2) : l;
}

template<>
inline unsigned count_significant_words<uint32_t, uint32_t>(uint32_t x) noexcept
{
    return x != 0 ? 1 : 0;
}

template<>
inline unsigned count_significant_words<uint64_t, uint64_t>(uint64_t x) noexcept
{
    return x != 0 ? 1 : 0;
}

template<typename Int>
inline std::tuple<Int, Int> udiv_qr_unr(Int x, Int y)
{
    // decent start
    unsigned c = clz(y);
    auto z = shl(Int(1), c);

    // z recurrence
    auto my = minus(y);
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
    return std::make_tuple(q, r);
}

inline std::tuple<uint256, uint256> udiv_qr_shift(uint256 x, uint256 y)
{
    uint256 r = x;
    uint256 q = 0;
    if (r >= y)
    {
        unsigned i = clz(y) - clz(r);
        y = y << i;
        // quotient computing phase
        for (;;)
        {
            if (r >= y)
            {
                r = r - y;
                q = q + 1;
            }
            if (i == 0)
                break;
            i = i - 1;
            q = q + q;
            y = y >> 1;
        }
    }
    return std::make_tuple(q, r);
}

std::tuple<uint256, uint256> udiv_qr_knuth_hd_base(uint256 x, uint256 y);
std::tuple<uint256, uint256> udiv_qr_knuth_llvm_base(uint256 u, uint256 v);
std::tuple<uint256, uint256> udiv_qr_knuth_opt_base(uint256 x, uint256 y);
std::tuple<uint256, uint256> udiv_qr_knuth_opt(uint256 x, uint256 y);

template<typename Int>
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

    return {q, r};
}

template<typename Int>
inline std::tuple<Int, Int> udiv_dc(Int u, Int v)
{
    using tr = traits<Int>;

    auto v1 = hi_half(v);
    auto v0 = lo_half(v);

    if (v1 == 0)
    {
        Int u1 = hi_half(u);
        if (u1 < v)
        {
            auto t = udiv_long(u, v0);
            return {std::get<0>(t), std::get<1>(t)};
        }
        else
        {
            auto u0 = lo_half(u);
            typename tr::half_type q1, k;
            std::tie(q1, k) = udiv_long(u1, v0);
            auto q0 = std::get<0>(udiv_long(join(k, u0), v0));
            Int q = join(q1, q0);
            Int r = u - v * q;
            return {q, r};
        }
    }
    unsigned n = clz(v);
    auto vn = v << n;
    auto vn1 = hi_half(vn);
    Int u1 = u >> 1;
    Int q1 = std::get<0>(udiv_long(u1, vn1));
    Int q0 = (q1 << n) >> 63;
    if (q0 != 0)
        q0 = q0 - 1;
    if ((u - q0 * v) >= v)
        q0 = q0 + 1;
    Int r = u - v * q0;
    return {q0, r};
}

inline std::string to_string(uint256 x)
{
    if (x == 0)
        return "0";

    std::string s;
    while (x != 0)
    {
        uint256 r;
        std::tie(x, r) = udiv_qr_unr(x, uint256(10));
        auto c = static_cast<size_t>(r);
        s.push_back(static_cast<char>('0' + c));
    }
    std::reverse(s.begin(), s.end());
    return s;
}

inline uint256 from_string(const std::string& s)
{
    uint256 x;

    for (auto c : s)
    {
        auto v = c - '0';
        x *= 10;
        x += v;
    }
    return x;
}


namespace experiments
{
/// Classic implementation of +=.
inline void add_to(uint256& a, uint128 b)
{
    a = add(a, b);
}

/// "Optimized" implementation of +=.
///
/// On clang-5 the results are these same, except the order of instructions
/// is different.
inline void add_to_opt(uint256& a, uint128 b)
{
    bool carry = false;
    std::tie(a.lo, carry) = add_with_carry(a.lo, b);
    a.hi += carry;
}
}
}


inline uint64_t add2(uint64_t ah, uint64_t al, uint64_t bh, uint64_t bl)
{
    (void)ah;
    auto l = al + bl;
    auto c = l < al;
    auto h = bh + bl + c;
    return h;
}

inline void add_128(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    // Intermediate values are used to avoid memory aliasing issues.
    auto l = a[0] + b[0];
    auto c = l < a[0];
    auto h = a[1] + b[1] + c;
    r[0] = l;
    r[1] = h;
}

inline bool adc_128(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    // Intermediate values are used to avoid memory aliasing issues.
    auto l = a[0] + b[0];
    auto c = l < a[0];
    auto h = a[1] + b[1];
    auto c1 = h < a[1];
    h += c;
    auto c2 = h < c;


    r[0] = l;
    r[1] = h;
    return c1 | c2;
}

inline void add_128(uint64_t* r, const uint64_t* a, uint64_t b)
{
    auto l = a[0] + b;
    auto c = l < a[0];
    auto h = a[1] + c;
    r[0] = l;
    r[1] = h;  // TODO: Do not store if not needed.
}

inline bool lt_128(const uint64_t* a, const uint64_t* b)
{
    if (a[1] < b[1])
        return true;
    return a[0] < b[0];
}

inline void add_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    uint64_t l[2];
    add_128(l, a, b);
    auto c = lt_128(a, b);
    uint64_t h[2];
    add_128(h, a + 2, b + 2);
    add_128(h, h, c);
    r[0] = l[0];
    r[1] = l[1];
    r[2] = h[0];
    r[3] = h[1];
}

inline void add2_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    uint64_t l[2];
    auto c = adc_128(l, a, b);
    uint64_t h[2];
    add_128(h, a + 2, b + 2);
    add_128(h, h, c);
    r[0] = l[0];
    r[1] = l[1];
    r[2] = h[0];
    r[3] = h[1];
}

inline bool add3_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    uint64_t l[4];
    bool c = 0;

    for (int i = 0; i < 4; ++i)
    {
        l[i] = a[i] + c;
        c = l[i] < c;

        l[i] += b[i];
        c |= l[i] < b[i];
    }

    r[0] = l[0];
    r[1] = l[1];
    r[2] = l[2];
    r[3] = l[3];
    return c;
}

inline void add_no_carry_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
    add3_256(r, a, b);
}

// uint256 operator+(uint256 a, uint256 b)
//{
//    uint256 r;
//    add_no_carry_256(r.limbs.data(), a.limbs.data(), b.limbs.data());
//    return r;
//}
//
// bool operator==(uint256 a, uint256 b)
//{
//    return std::equal(a.limbs.begin(), a.limbs.end(), b.limbs.begin());
//}
