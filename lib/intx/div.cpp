// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div.hpp"

namespace intx
{
struct normalized_args64
{
    using word_type = uint64_t;
    std::array<word_type, sizeof(uint512) / sizeof(word_type) + 1> numerator;
    std::array<word_type, sizeof(uint512) / sizeof(word_type)> denominator;
    int num_numerator_words;
    int num_denominator_words;
    int shift;
};

inline normalized_args64 normalize64(const uint512& numerator, const uint512& denominator) noexcept
{
    static constexpr auto num_words = int{sizeof(uint512) / sizeof(normalized_args64::word_type)};

    auto* u = reinterpret_cast<const normalized_args64::word_type*>(&numerator);
    auto* v = reinterpret_cast<const normalized_args64::word_type*>(&denominator);

    normalized_args64 na;
    auto* un = &na.numerator[0];
    auto* vn = &na.denominator[0];

    auto& m = na.num_numerator_words;
    for (m = num_words; m > 0 && u[m - 1] == 0; --m)
        ;

    auto& n = na.num_denominator_words;
    for (n = num_words; n > 0 && v[n - 1] == 0; --n)
        ;

    na.shift = builtins::clz(v[n - 1]);
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
        un[num_words] = 0;
        std::memcpy(un, u, sizeof(numerator));
        std::memcpy(vn, v, sizeof(denominator));
    }

    return na;
}

namespace
{
union uint512_words
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    const uint512 number;
    uint32_t words[num_words];

    constexpr explicit uint512_words(uint512 number = {}) noexcept : number{number} {}

    uint32_t& operator[](size_t index) { return words[index]; }
};

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

div_result<uint512> udivrem32(const uint512& u, const uint512& v) noexcept
{
    auto na = normalize(u, v);
    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    return udivrem_knuth(na);
}

div_result<uint256> udivrem(const uint256& u, const uint256& v) noexcept
{
    auto x = udivrem(uint512{u}, uint512{v});
    return {x.quot.lo, x.rem.lo};
}

div_result<uint512> udivrem(const uint512& u, const uint512& v) noexcept
{
    const auto na = normalize64(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return udivrem_by1(na);

    if (na.num_denominator_words == 2)
        return udivrem_by2(na);

    // Fallback to udivrem32().
    return udivrem32(u, v);
}

}  // namespace intx
