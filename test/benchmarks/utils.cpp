// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

#include <cstring>

using namespace intx;

uint128 div_gcc(uint128 x, uint128 y) noexcept
{
    unsigned __int128 u, v;
    std::memcpy(&u, &x, sizeof(u));
    std::memcpy(&v, &y, sizeof(v));
    auto q = u / y;
    return *(uint128*)&q;
}
