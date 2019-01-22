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

div_result<uint512> udivrem_knuth64(const normalized_args64& na) noexcept
{
    auto n = na.num_denominator_words;
    auto m = na.num_numerator_words;

    auto vn = na.denominator;
    auto un = na.numerator;

    uint512_words64 q;
    uint512_words64 r;

    constexpr auto base = uint128{1} << 64;
    for (int j = m - n; j >= 0; j--)
    {
        uint128 qhat, rhat;
        uint64_t divisor = vn[n - 1];
        uint128 dividend = join(un[j + n], un[j + n - 1]);
        if (hi_half(dividend) >= divisor)  // Will overflow:
        {
            qhat = base;
            rhat = dividend - qhat * divisor;
        }
        else
        {
            auto res = udivrem_long(dividend, divisor);
            qhat = res.quot;
            rhat = res.rem;
        }

        uint64_t next_divisor = vn[n - 2];
        uint128 pd = join(lo_half(rhat), un[j + n - 2]);
        if (qhat == base || qhat * next_divisor > pd)
        {
            --qhat;
            rhat += divisor;
            pd = join(lo_half(rhat), un[j + n - 2]);
            if (rhat < base && (qhat == base || qhat * next_divisor > pd))
                --qhat;
        }

        // Multiply and subtract.
        __int128 borrow = 0;
        for (int i = 0; i < n; i++)
        {
            uint128 p = qhat * vn[i];
            __int128 t = __int128(un[i + j]) - borrow - lo_half(p);
            uint128 s = static_cast<uint128>(t);
            un[i + j] = lo_half(s);
            borrow = hi_half(p) - hi_half(s);
        }
        __int128 t = un[j + n] - borrow;
        un[j + n] = static_cast<uint64_t>(t);

        q[j] = lo_half(qhat);  // Store quotient digit.

        if (t < 0)
        {            // If we subtracted too
            --q[j];  // much, add back.
            uint128 carry = 0;
            for (int i = 0; i < n; ++i)
            {
                // TODO: Consider using bool carry. See LLVM version.
                uint128 u_tmp = uint128(un[i + j]) + uint128(vn[i]) + carry;
                un[i + j] = lo_half(u_tmp);
                carry = hi_half(u_tmp);
            }
            un[j + n] = lo_half(uint128(un[j + n]) + carry);
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
    const auto na = normalize64(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
        return udivrem_by1(na);

    if (na.num_denominator_words == 2)
        return udivrem_by2(na);

    return udivrem_knuth64(na);
}

}  // namespace intx
