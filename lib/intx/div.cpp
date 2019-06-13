// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div.hpp"

namespace intx
{
namespace
{
union uint512_words64
{
    using word_type = uint64_t;

    const uint512 number;
    word_type words[uint512::num_words];

    constexpr explicit uint512_words64(uint512 x = {}) noexcept : number{x} {}

    word_type& operator[](size_t index) { return words[index]; }
};

inline div_result<uint512> udivrem_by1(const normalized_div_args<512>& na) noexcept
{
    auto u = as_words(na.numerator);
    auto d = as_words(na.denominator)[0];
    auto v = reciprocal_2by1(d);

    auto q = uint512_words64{};

    auto x = div_result<decltype(q)::word_type>{0, na.numerator_ex};

    // OPT: Skip leading zero words.
    for (int j = uint512::num_words - 1; j >= 0; --j)
    {
        x = udivrem_2by1({x.rem, u[j]}, d, v);
        q[j] = x.quot;
    }

    return {q.number, x.rem >> na.shift};
}

inline div_result<uint512> udivrem_by2(const normalized_div_args<512>& na) noexcept
{
    auto u = as_words(na.numerator);
    auto dw = as_words(na.denominator);
    auto d = uint128{dw[1], dw[0]};
    auto v = reciprocal_3by2(d);

    auto q = uint512_words64{};
    constexpr auto num_words = uint512::num_words;

    auto r = uint128{u[num_words], u[num_words - 1]};

    // OPT: Skip leading zero words.
    for (int j = num_words - 2; j >= 0; --j)
    {
        auto res = udivrem_3by2(r.hi, r.lo, u[j], d, v);
        q[j] = res.quot.lo;
        r = res.rem;
    }

    return {q.number, r >> na.shift};
}

void udivrem_knuth(uint64_t q[], uint64_t un[], int m, const uint64_t vn[], int n) noexcept
{
    const auto divisor = uint128{vn[n - 1], vn[n - 2]};
    const auto reciprocal = reciprocal_2by1(divisor.hi);
    for (int j = m - n; j >= 0; --j)
    {
        const auto u2 = un[j + n];
        const auto u1 = un[j + n - 1];
        const auto u0 = un[j + n - 2];

        uint64_t qhat;
        uint128 rhat;
        const auto dividend = uint128{u2, u1};
        if (dividend.hi >= divisor.hi)  // Will overflow:
        {
            qhat = ~uint64_t{0};
            rhat = dividend - uint128{divisor.hi, 0};
            rhat += divisor.hi;

            // Adjustment.
            // OPT: This is not needed but helps avoiding negative case.
            if (rhat.hi == 0 && umul(qhat, divisor.lo) > uint128{rhat.lo, u0})
                --qhat;
        }
        else
        {
            auto res = udivrem_2by1(dividend, divisor.hi, reciprocal);
            qhat = res.quot;
            rhat = res.rem;

            if (umul(qhat, divisor.lo) > uint128{rhat.lo, u0})
            {
                --qhat;
                rhat += divisor.hi;

                // Adjustment.
                // OPT: This is not needed but helps avoiding negative case.
                if (rhat.hi == 0 && umul(qhat, divisor.lo) > uint128{rhat.lo, u0})
                    --qhat;
            }
        }

        // Multiply and subtract.
        uint64_t borrow = 0;
        for (int i = 0; i < n; ++i)
        {
            const auto p = umul(qhat, vn[i]);
            const auto s = uint128{un[i + j]} - borrow - p.lo;
            un[i + j] = s.lo;
            borrow = p.hi - s.hi;
        }

        un[j + n] = u2 - borrow;
        if (u2 < borrow)  // Too much subtracted, add back.
        {
            --qhat;

            uint64_t carry = 0;
            for (int i = 0; i < n; ++i)
            {
                auto s = uint128{un[i + j]} + vn[i] + carry;
                un[i + j] = s.lo;
                carry = s.hi;
            }
            un[j + n] += carry;

            // TODO: Consider this alternative implementation:
            // bool k = false;
            // for (int i = 0; i < n; ++i) {
            //     auto limit = std::min(un[j+i],vn[i]);
            //     un[i + j] += vn[i] + k;
            //     k = un[i + j] < limit || (k && un[i + j] == limit);
            // }
            // un[j+n] += k;
        }

        // OPT: We can avoid allocating q, un can re used to store quotient.
        q[j] = qhat;  // Store quotient digit.
    }
}

inline div_result<uint512> udivrem_knuth_wrapper(normalized_div_args<512>& na) noexcept
{
    auto n = na.num_denominator_words;
    auto m = na.num_numerator_words;

    auto un = as_words(na.numerator);  // Will be modified.

    uint512 q;
    uint512_words64 r;

    udivrem_knuth(as_words(q), &un[0], m, as_words(na.denominator), n);

    for (int i = 0; i < n; ++i)
        r[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];

    return {q, r.number};
}
}  // namespace

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept
{
    auto x = udivrem(uint512{u}, uint512{v});
    return {x.quot.lo, x.rem.lo};
}

div_result<uint512> udivrem(const uint512& u, const uint512& v) noexcept
{
    auto na = normalize(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return udivrem_by1(na);

    if (na.num_denominator_words == 2)
        return udivrem_by2(na);

    return udivrem_knuth_wrapper(na);
}

}  // namespace intx
