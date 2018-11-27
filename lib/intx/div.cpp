// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include "div.hpp"

#include <iostream>

namespace intx
{
namespace div
{
namespace
{
inline std::tuple<uint64_t, uint64_t> udivrem(uint64_t u, uint64_t v) noexcept
{
    return {u / v, u % v};
}

inline std::tuple<uint512, uint32_t> udivrem_1(const uint512& x, uint32_t v)
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    uint32_t r = 0;
    uint512 qq = 0;
    auto* u = reinterpret_cast<const uint32_t*>(&x);
    auto* q = reinterpret_cast<uint32_t*>(&qq);

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q[j], r) = udivrem(join(r, u[j]), v);
    return {qq, r};
}

std::tuple<uint512, uint512> udivrem_knuth(div::normalized_args& na) noexcept
{
    // b denotes the base of the number system. In our case b is 2^32.
    constexpr uint64_t b = uint64_t(1) << 32;

    auto* u = &na.numerator[0];
    auto* v = &na.denominator[0];
    auto m = na.num_numerator_words - na.num_denominator_words;
    auto n = na.num_denominator_words;

    uint512 qq;
    uint512 rr;
    auto* q = reinterpret_cast<uint32_t*>(&qq);
    auto* r = reinterpret_cast<uint32_t*>(&rr);

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
    return {qq, rr};
}
}  // namespace
}  // namespace div

std::tuple<uint512, uint512> udivrem(const uint512& u, const uint512& v)
{
    auto na = div::normalize(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return div::udivrem_1(u, static_cast<uint32_t>(v.lo.lo));

    return div::udivrem_knuth(na);
}

std::tuple<uint256, uint256> udivrem(const uint256& u, const uint256& v)
{
    auto x = udivrem(uint512(u), uint512(v));
    return {std::get<0>(x).lo, std::get<1>(x).lo};
}

}  // namespace intx
