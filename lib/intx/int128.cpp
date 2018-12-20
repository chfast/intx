// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

namespace intx
{
namespace
{
template <typename T>
struct div_result
{
    T quot;
    T rem;
};

inline div_result<uint64_t> udivrem_long(uint128 u, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(u.hi), "a"(u.lo), "g"(v));
    return {q, r};
}

div_result<uint128> udivrem(uint128 x, uint128 y) noexcept
{
    if (y.hi == 0)
    {
        auto res = udivrem_long({x.hi % y.lo, x.lo}, y.lo);
        return {{x.hi / y.lo, res.quot}, res.rem};
    }

    int shift = builtins::clz(y.hi);
    uint128 vn = y << shift;
    uint128 un = x << shift;
    uint64_t unx = shift ? x.hi >> (64 - shift) : 0;

    auto res = udivrem_long({unx, un.hi}, vn.hi);
    if (uint128(res.quot) * vn.lo > uint128{res.rem, un.lo})
        res.quot -= 1;  // TODO: Implement ++ / --.

    return {res.quot, x - (y * res.quot)};
}

}  // namespace

uint128 operator/(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).quot;
}

uint128 operator%(uint128 x, uint128 y) noexcept
{
    return udivrem(x, y).rem;
}

}  // namespace intx
