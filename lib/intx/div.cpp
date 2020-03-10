// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "div.hpp"
#include <cassert>
#include <tuple>

#if defined(_MSC_VER)
#define UNREACHABLE __assume(0)
#else
#define UNREACHABLE __builtin_unreachable()
#endif

#if defined(_MSC_VER)
#define UNLIKELY(EXPR) EXPR
#else
#define UNLIKELY(EXPR) __builtin_expect((bool)(EXPR), false)
#endif

#if defined(NDEBUG)
#define REQUIRE(X) \
    if (!(X))      \
    UNREACHABLE
#else
#define REQUIRE assert
#endif

namespace intx
{
namespace
{
/// Divides arbitrary long unsigned integer by 64-bit unsigned integer (1 word).
/// @param u    The array of a normalized numerator words. It will contain
///             the quotient after execution.
/// @param len  The number of numerator words.
/// @param d    The normalized denominator.
/// @return     The remainder.
inline uint64_t udivrem_by1(uint64_t u[], int len, uint64_t d) noexcept
{
    REQUIRE(len >= 1);  // TODO: Make it >= 2.

    const auto reciprocal = reciprocal_2by1(d);

    auto r = u[len - 1];  // Set the top word as remainder.
    u[len - 1] = 0;       // Reset the word being a part of the result quotient.

    for (int j = len - 2; j >= 0; --j)
    {
        const auto x = udivrem_2by1({r, u[j]}, d, reciprocal);
        u[j] = x.quot;
        r = x.rem;
    }

    return r;
}

/// Divides arbitrary long unsigned integer by 128-bit unsigned integer (2 words).
/// @param u    The array of a normalized numerator words. It will contain the
///             quotient after execution.
/// @param len  The number of numerator words.
/// @param d    The normalized denominator.
/// @return     The remainder.
inline uint128 udivrem_by2(uint64_t u[], int len, uint128 d) noexcept
{
    REQUIRE(len >= 2);  // TODO: Make it >= 3.

    const auto reciprocal = reciprocal_3by2(d);

    auto r = uint128{u[len - 1], u[len - 2]};  // Set the 2 top words as remainder.
    u[len - 1] = u[len - 2] = 0;  // Reset these words being a part of the result quotient.

    for (int j = len - 3; j >= 0; --j)
        std::tie(u[j], r) = udivrem_3by2(r.hi, r.lo, u[j], d, reciprocal);

    return r;
}

/// s = x + y.
inline bool add(uint64_t s[], const uint64_t x[], const uint64_t y[], int len) noexcept
{
    // OPT: Add MinLen template parameter and unroll first loop iterations.
    REQUIRE(len >= 2);

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
    REQUIRE(len >= 3);

    uint64_t borrow = 0;
    for (int i = 0; i < len; ++i)
    {
        const auto s = sub_with_carry(x[i], borrow);
        const auto p = umul(y[i], multiplier);
        const auto t = sub_with_carry(s.value, p.lo);
        r[i] = t.value;
        borrow = p.hi + s.carry + t.carry;
    }
    return borrow;
}

void udivrem_knuth(uint64_t q[], uint64_t u[], int ulen, const uint64_t d[], int dlen) noexcept
{
    REQUIRE(dlen >= 3);
    REQUIRE(ulen >= dlen);

    const auto divisor = uint128{d[dlen - 1], d[dlen - 2]};
    const auto reciprocal = reciprocal_2by1(divisor.hi);
    for (int j = ulen - dlen - 1; j >= 0; --j)
    {
        const auto u2 = u[j + dlen];
        const auto u1 = u[j + dlen - 1];
        const auto u0 = u[j + dlen - 2];

        uint64_t qhat;
        uint128 rhat;
        const auto numerator = uint128{u2, u1};
        if (UNLIKELY(numerator.hi >= divisor.hi))  // Division overflows.
        {
            qhat = ~uint64_t{0};
            rhat = numerator - uint128{divisor.hi, 0};
            rhat += divisor.hi;

            // Adjustment (not needed for correctness, but helps avoiding "add back" case).
            if (rhat.hi == 0 && umul(qhat, divisor.lo) > uint128{rhat.lo, u0})
                --qhat;
        }
        else
        {
            const auto res = udivrem_2by1(numerator, divisor.hi, reciprocal);
            qhat = res.quot;
            rhat = res.rem;

            const auto p = umul(qhat, divisor.lo);
            if (p > uint128{rhat.lo, u0})
            {
                --qhat;
                rhat += divisor.hi;

                // Adjustment (not needed for correctness, but helps avoiding "add back" case).
                if (rhat.hi == 0 && (p - divisor.lo) > uint128{rhat.lo, u0})
                    --qhat;
            }
        }

        // Multiply and subtract.
        bool carry;
        const auto overflow = submul(&u[j], &u[j], d, dlen, qhat);
        std::tie(u[j + dlen], carry) = sub_with_carry(u2, overflow);
        if (carry)  // Too much subtracted, add back.
        {
            --qhat;
            u[j + dlen - 1] += divisor.hi + add(&u[j], &u[j], d, dlen - 1);
        }

        q[j] = qhat;  // Store quotient digit.
    }
}

}  // namespace

template <unsigned N>
div_result<uint<N>> udivrem(const uint<N>& u, const uint<N>& v) noexcept
{
    auto na = normalize(u, v);

    if (na.num_denominator_words > na.num_numerator_words)
        return {0, u};

    if (na.num_denominator_words == 1)
    {
        auto r = udivrem_by1(
            as_words(na.numerator), na.num_numerator_words, as_words(na.denominator)[0]);
        return {na.numerator, r >> na.shift};
    }

    if (na.num_denominator_words == 2)
    {
        auto d = as_words(na.denominator);
        auto r = udivrem_by2(as_words(na.numerator), na.num_numerator_words, {d[1], d[0]});
        return {na.numerator, r >> na.shift};
    }

    auto un = as_words(na.numerator);  // Will be modified.

    uint<N> q;

    udivrem_knuth(as_words(q), &un[0], na.num_numerator_words, as_words(na.denominator),
        na.num_denominator_words);

    uint<N> r;
    auto rw = as_words(r);
    for (int i = 0; i < na.num_denominator_words - 1; ++i)
        rw[i] = na.shift ? (un[i] >> na.shift) | (un[i + 1] << (64 - na.shift)) : un[i];
    rw[na.num_denominator_words - 1] = un[na.num_denominator_words - 1] >> na.shift;

    return {q, r};
}

template div_result<uint<256>> udivrem(const uint<256>& u, const uint<256>& v) noexcept;
template div_result<uint<512>> udivrem(const uint<512>& u, const uint<512>& v) noexcept;
template div_result<uint<1024>> udivrem(const uint<1024>& u, const uint<1024>& v) noexcept;
template div_result<uint<2048>> udivrem(const uint<2048>& u, const uint<2048>& v) noexcept;
template div_result<uint<4096>> udivrem(const uint<4096>& u, const uint<4096>& v) noexcept;

}  // namespace intx
