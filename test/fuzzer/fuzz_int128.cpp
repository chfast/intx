// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <cstring>
#include <intx/int128.hpp>

using namespace intx;

enum class op
{
    div
};

inline void expect_eq(uint128 a, unsigned __int128 b) noexcept
{
    uint128 c = *(uint128*)&b;
    if (a != c)
        __builtin_trap();
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
{
    if (size != 33)
        return 0;

    uint128 a, b;
    constexpr auto s = sizeof(uint128);
    std::memcpy(&a, &data[1], s);
    std::memcpy(&b, &data[1 + s], s);

    unsigned __int128 u, v;
    std::memcpy(&u, &data[1], s);
    std::memcpy(&v, &data[1 + s], s);

    switch (op(data[0]))
    {
    case op::div:
        if (v != 0)
            expect_eq(a / b, u / v);

    default:
        break;
    }

    return 0;
}