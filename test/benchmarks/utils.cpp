// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/int128.hpp>

using namespace intx;

uint128 div_gcc(uint128 x, uint128 y) noexcept
{
    auto q = (*(unsigned __int128*)&x) / (*(unsigned __int128*)&y);
    return *(uint128*)&q;
}
