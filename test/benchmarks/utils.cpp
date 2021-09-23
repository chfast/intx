// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>
#include <cstdint>
#include <cstring>

uint64_t udiv_native(uint64_t x, uint64_t y) noexcept
{
    return x / y;
}

uint64_t nop(uint64_t x, uint64_t y) noexcept
{
    return x ^ y;
}

intx::uint128 div_gcc(intx::uint128 x, intx::uint128 y) noexcept
{
    return intx::builtin_uint128{x} / intx::builtin_uint128{y};
}

inline uint64_t umulh(uint64_t x, uint64_t y)
{
    const auto p = intx::builtin_uint128{x} * intx::builtin_uint128{y};
    return static_cast<uint64_t>(p >> 64);
}

uint64_t soft_div_unr_unrolled(uint64_t x, uint64_t y) noexcept
{
    INTX_REQUIRE(y != 0);

    // decent start
    uint64_t z = uint64_t(1) << intx::clz(y);

    // z recurrence, 6 iterations (TODO: make sure 6 is enough)
    uint64_t my = 0 - y;
    for (int i = 0; i < 6; ++i)
        z += umulh(z, my * z);

    // q estimate
    uint64_t q = umulh(x, z);
    uint64_t r = x - (y * q);

    // q refinement
    if (r >= y)
    {
        r -= y;
        q += 1;

        if (r >= y)
        {
            // r -= y;
            q += 1;
        }
    }
    return q;
}

uint64_t soft_div_unr(uint64_t x, uint64_t y) noexcept
{
    INTX_REQUIRE(y != 0);

    // decent start
    uint64_t z = uint64_t(1) << intx::clz(y);

    // z recurrence
    uint64_t my = 0 - y;
    for (int i = 0; i < 6; ++i)
    {
        uint64_t zd = umulh(z, my * z);
        if (zd == 0)
            break;
        z = z + zd;
    }

    // q estimate
    uint64_t q = umulh(x, z);
    uint64_t r = x - (y * q);
    // q refinement
    if (r >= y)
    {
        r = r - y;
        q = q + 1;
        if (r >= y)
        {
            // r = r - y;
            q = q + 1;
        }
    }
    return q;
}
