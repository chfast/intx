// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include "../utils/gmp.hpp"
#include <cstring>

using namespace intx;

enum class op
{
    divrem,
};

template <typename T>
inline void expect_eq(const T& x, const T& y) noexcept
{
    if (x != y)
        __builtin_trap();
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
{
    static constexpr auto s = sizeof(uint512);
    if (size != 2 * s + 1)
        return 0;

    uint512 a, b;
    // FIXME: Add bswap()
    std::memcpy(&a, &data[1], s);
    std::memcpy(&b, &data[1 + s], s);
    a = bswap(a);
    b = bswap(b);

    switch (op(data[0]))
    {
    case op::divrem:
        if (b != 0)
        {
            auto x = udivrem(a, b);
            auto y = gmp_udiv_qr(a, b);
            expect_eq(std::get<0>(x), std::get<0>(y));
            expect_eq(std::get<1>(x), std::get<1>(y));
        }

    default:
        break;
    }

    return 0;
}