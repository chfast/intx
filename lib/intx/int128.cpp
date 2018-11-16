// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

#include <tuple>

namespace intx
{
namespace
{

template<typename T>
struct div_result
{
    T q;
    T r;
};


inline div_result<uint64_t> udivrem_long(uint128 u, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(u.hi), "a"(u.lo), "g"(v));
    return {q, r};
}

void udiv_knuth_internal_64(
    uint64_t q[], uint64_t r[], const uint64_t u[], const uint64_t v[], int m, int n)
{
    // Normalize by shifting the divisor v left so that its highest bit is on,
    // and shift the dividend u left the same amount.
    auto vn = static_cast<uint64_t*>(alloca(n * sizeof(uint64_t)));
    auto un = static_cast<uint64_t*>(alloca((m + 1) * sizeof(uint64_t)));

    unsigned shift = builtins::clz(v[n - 1]);
    unsigned lshift = 64 - shift;

    for (int i = n - 1; i > 0; i--)
        vn[i] = shift ? (v[i] << shift) | (v[i - 1] >> lshift) : v[i];
    vn[0] = v[0] << shift;

    un[m] = shift != 0 ? u[m - 1] >> lshift : 0;
    for (int i = m - 1; i > 0; i--)
        un[i] = shift ? (u[i] << shift) | (u[i - 1] >> lshift) : u[i];
    un[0] = u[0] << shift;

    constexpr uint128 base = uint128(1) << 64;  // Number base (32 bits).
    for (int j = m - n; j >= 0; j--)  // Main loop.
    {
        uint128 qhat, rhat;
        uint64_t divisor = vn[n - 1];
        uint128 dividend{un[j + n], un[j + n - 1]};
        if (dividend.hi >= divisor)  // Will overflow:
        {
            qhat = base;
            rhat = dividend - qhat * divisor;
        }
        else
        {
            auto res = udivrem_long(dividend, divisor);
            qhat = res.q;
            rhat = res.r;
        }

        uint64_t next_divisor = vn[n - 2];
        uint128 pd{rhat.lo, un[j + n - 2]};
        if (qhat == base || qhat * next_divisor > pd)
        {
            qhat -= 1;  // TODO: Implement ++ / --.
            rhat += divisor;
            pd = uint128{rhat.lo, un[j + n - 2]};
            if (rhat < base && (qhat == base || qhat * next_divisor > pd))
                qhat -= 1;
        }

        // Multiply and subtract.
        __int128 borrow = 0;
        for (int i = 0; i < n; i++)
        {
            uint128 p = qhat * vn[i];
            __int128 t = __int128(un[i + j]) - borrow - p.lo;
            unsigned __int128 ut(t);
            uint128 s{uint64_t(ut >> 64), uint64_t(ut)};
            un[i+j] = s.lo;
            borrow = p.hi - s.hi;
        }
        __int128 t = un[j + n] - borrow;
        un[j + n] = static_cast<uint64_t>(t);

        q[j] = qhat.lo; // Store quotient digit.

        if (t < 0)
        {            // If we subtracted too
            --q[j];  // much, add back.
            uint128 carry = 0;
            for (int i = 0; i < n; ++i)
            {
                // TODO: Consider using bool carry. See LLVM version.
                uint128 u_tmp = uint128(un[i + j]) + uint128(vn[i]) + carry;
                un[i + j] = u_tmp.lo;
                carry = u_tmp.hi;
            }
            un[j + n] = (uint128(un[j + n]) + carry).lo;
        }
    }

    for (int i = 0; i < n; ++i)
        r[i] = shift ? (un[i] >> shift) | (un[i + 1] << lshift) : un[i];
}

inline div_result<uint128> udivrem_1(const uint128& x, uint64_t y)
{
    auto res = udivrem_long({x.hi % y, x.lo}, y);
    return {{x.hi / y, res.q}, res.r};
}

div_result<uint128> udivrem_128_knuth_64(uint128 x, uint128 y)
{
    if (y.hi == 0)                  // XX
        return udivrem_1(x, y.lo);  // 0K

    if (x.hi == 0)      // 0X
        return {0, x};  // KX

    uint128 q, r;
    udiv_knuth_internal_64(&q.lo, &r.lo, &x.lo, &y.lo, 2, 2);
    return {q, r};
}


}  // namespace

uint128 operator/(const uint128& x, const uint128& y) noexcept
{
    return udivrem_128_knuth_64(x, y).q;
}

uint128 operator%(const uint128& x, const uint128& y) noexcept
{
    return udivrem_128_knuth_64(x, y).r;
}

}  // namespace intx
