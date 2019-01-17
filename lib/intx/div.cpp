// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div.hpp"

namespace intx
{
namespace
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
}  // namespace


/// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
///
/// Based on Algorithm 2 from "Improved division by invariant integers".
uint64_t reciprocal(uint64_t d) noexcept
{
    auto d9 = uint8_t(d >> 55);
    auto v0 = uint64_t{reciprocal_table[d9]};

    auto d40 = (d >> 24) + 1;
    auto v1 = (v0 << 11) - (v0 * v0 * d40 >> 40) - 1;

    auto v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    auto d0 = d % 2;
    auto d63 = d / 2 + d0;  // ceil(d/2)
    auto e = ((v2 / 2) & -d0) - v2 * d63;
    auto mh = (uint128{v2} * e).hi;  // umulh
    auto v3 = (v2 << 31) + (mh >> 1);

    // OPT: The compiler tries a bit too much with 128 + 64 addition and ends up using subtraction.
    //      Compare with __int128.
    auto mf = uint128{v3} * d;  // full mul
    auto m = internal::optimized_add(mf, d);
    auto v3a = m.hi + d;

    auto v4 = v3 - v3a;

    return v4;
}

uint64_t reciprocal_3by2(uint128 d) noexcept
{
    auto v = reciprocal(d.hi);
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

    auto t = uint128{v} * d.lo;

    p += t.hi;
    if (p < t.hi)
    {
        --v;
        if (uint128{p, t.lo} >= d)
            --v;
    }
    return v;
}

div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept
{
    auto q = uint128{v} * u.hi;
    q = internal::optimized_add(q, u);

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

div_result<uint128> udivrem_3by2(uint64_t u2, uint64_t u1, uint64_t u0, uint128 d) noexcept
{
    auto v = reciprocal_3by2(d);
    auto q = uint128{v} * u2;
    q = internal::optimized_add(q, {u2, u1});

    auto r1 = u1 - q.hi * d.hi;

    auto t = uint128{d.lo} * q.hi;

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

namespace
{
inline std::tuple<uint64_t, uint64_t> udivrem(uint64_t u, uint64_t v) noexcept
{
    return {u / v, u % v};
}

union uint512_words
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    const uint512 number;
    uint32_t words[num_words];

    constexpr explicit uint512_words(uint512 number = {}) noexcept : number{number} {}

    uint32_t& operator[](size_t index) { return words[index]; }
};

inline div_result<uint512> udivrem_1(const uint512& x, uint32_t v)
{
    uint32_t r = 0;
    uint512_words q;
    uint512_words u{x};

    for (int j = decltype(q)::num_words - 1; j >= 0; --j)
        std::tie(q[j], r) = udivrem(join(r, u[j]), v);
    return {q.number, r};
}

div_result<uint512> udivrem_knuth(normalized_args& na) noexcept
{
    // b denotes the base of the number system. In our case b is 2^32.
    constexpr uint64_t b = uint64_t(1) << 32;

    auto* u = &na.numerator[0];
    auto* v = &na.denominator[0];
    auto m = na.num_numerator_words - na.num_denominator_words;
    auto n = na.num_denominator_words;

    uint512_words q;
    uint512_words r;

    int j = m;
    do
    {
        uint64_t dividend = join(u[j + n], u[j + n - 1]);

        uint64_t qp, rp;
        if (u[j + n] >= v[n - 1])
        {
            // Overflow:
            qp = b;
            rp = dividend - qp * v[n - 1];
        }
        else
        {
            qp = dividend / v[n - 1];
            rp = dividend % v[n - 1];
        }


        if (qp == b || qp * v[n - 2] > b * rp + u[j + n - 2])
        {
            qp--;
            rp += v[n - 1];
            if (rp < b && (qp == b || qp * v[n - 2] > b * rp + u[j + n - 2]))
                qp--;
        }

        int64_t borrow = 0;
        for (int i = 0; i < n; ++i)
        {
            uint64_t p = qp * v[i];
            uint64_t subres = int64_t(u[j + i]) - borrow - intx::lo_half(p);
            u[j + i] = intx::lo_half(subres);
            borrow = intx::hi_half(p) - intx::hi_half(subres);
        }
        bool isNeg = u[j + n] < borrow;
        u[j + n] -= intx::lo_half(static_cast<uint64_t>(borrow));

        q[j] = intx::lo_half(qp);
        if (isNeg)
        {
            q[j]--;
            bool carry = false;
            for (int i = 0; i < n; i++)
            {
                uint32_t limit = std::min(u[j + i], v[i]);
                u[j + i] += v[i] + carry;
                carry = u[j + i] < limit || (carry && u[j + i] == limit);
            }
            u[j + n] += carry;
        }

    } while (--j >= 0);

    if (na.shift)
    {
        uint32_t carry = 0;
        for (int i = n - 1; i >= 0; i--)
        {
            r[i] = (u[i] >> na.shift) | carry;
            carry = u[i] << (32 - na.shift);
        }
    }
    else
    {
        for (int i = n - 1; i >= 0; i--)
            r[i] = u[i];
    }
    return {q.number, r.number};
}
}  // namespace

div_result<uint512> udivrem(const uint512& u, const uint512& v) noexcept
{
    auto na = normalize(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return udivrem_1(u, static_cast<uint32_t>(v.lo.lo.lo));

    return udivrem_knuth(na);
}

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept
{
    auto x = udivrem(uint512{u}, uint512{v});
    return {x.quot.lo, x.rem.lo};
}

}  // namespace intx
