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
    static constexpr int num_words = sizeof(uint512) / sizeof(word_type);

    const uint512 number;
    word_type words[num_words];

    constexpr explicit uint512_words64(uint512 number = {}) noexcept : number{number} {}

    word_type& operator[](size_t index) { return words[index]; }
};

inline div_result<uint512> udivrem_by1(const normalized_args64& na) noexcept
{
    auto d = na.denominator[0];
    auto v = reciprocal(d);

    auto q = uint512_words64{};
    constexpr auto num_words = decltype(q)::num_words;

    auto x = div_result<decltype(q)::word_type>{0, na.numerator[num_words]};

    // OPT: Skip leading zero words.
    for (int j = num_words - 1; j >= 0; --j)
    {
        x = udivrem_2by1({x.rem, na.numerator[j]}, d, v);
        q[j] = x.quot;
    }

    return {q.number, x.rem >> na.shift};
}

inline div_result<uint512> udivrem_by2(const normalized_args64& na) noexcept
{
    auto d = uint128{na.denominator[1], na.denominator[0]};
    auto v = reciprocal_3by2(d);

    auto q = uint512_words64{};
    constexpr auto num_words = decltype(q)::num_words;

    auto r = uint128{na.numerator[num_words], na.numerator[num_words - 1]};

    // OPT: Skip leading zero words.
    for (int j = num_words - 2; j >= 0; --j)
    {
        auto res = udivrem_3by2(r.hi, r.lo, na.numerator[j], d, v);
        q[j] = res.quot.lo;
        r = res.rem;
    }

    // TODO: Add conversion uint128 -> uint512.
    return {q.number, uint256{r >> na.shift}};
}

div_result<uint512> udivrem_knuth(normalized_args64& na) noexcept
{
    auto n = na.num_denominator_words;
    auto m = na.num_numerator_words;

    const auto& vn = na.denominator;
    auto& un = na.numerator;  // Will be modified.

    uint512_words64 q;
    uint512_words64 r;

    constexpr auto base = uint128{1, 0};
    const auto divisor = uint128{vn[n - 1], vn[n - 2]};
    for (int j = m - n; j >= 0; --j)
    {
        div_result<uint128> h;
        const auto dividend = uint128{un[j + n], un[j + n - 1]};
        if (dividend.hi >= divisor.hi)  // Will overflow:
        {
            h = {base, dividend - uint128{divisor.hi, 0}};
        }
        else
        {
            auto res = udivrem_long(dividend, divisor.hi);
            h = {res.quot, res.rem};
        }

        auto pd = uint128{h.rem.lo, un[j + n - 2]};
        if (h.quot == base || h.quot * divisor.lo > pd)
        {
            --h.quot;
            h.rem += divisor.hi;
            pd = uint128{h.rem.lo, un[j + n - 2]};
            if (h.rem < base && h.quot * divisor.lo > pd)
                --h.quot;
        }

        // Multiply and subtract.
        uint64_t borrow = 0;
        for (int i = 0; i < n; ++i)
        {
            const auto p = h.quot.lo * uint128{vn[i]};  // Full mul.
            const auto s = uint128{un[i + j]} - borrow - p.lo;
            un[i + j] = s.lo;
            borrow = p.hi - s.hi;
        }
        q[j] = h.quot.lo;  // Store quotient digit.

        const bool neg = un[j + n] < borrow;
        un[j + n] -= borrow;
        if (neg)  // Too much subtracted, add back.
        {
            --q[j];

            uint64_t carry = 0;
            for (int i = 0; i < n; ++i)
            {
                auto s = uint128(un[i + j]) + vn[i] + carry;
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
    }

    for (int i = 0; i < n; ++i)
        r[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];

    return {q.number, r.number};
}
}  // namespace

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept
{
    auto x = udivrem(uint512{u}, uint512{v});
    return {x.quot.lo, x.rem.lo};
}

div_result<uint512> udivrem(const uint512& u, const uint512& v) noexcept
{
    auto na = normalize64(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return udivrem_by1(na);

    if (na.num_denominator_words == 2)
        return udivrem_by2(na);

    return udivrem_knuth(na);
}

}  // namespace intx
