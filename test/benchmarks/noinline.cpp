// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>

using namespace intx;

auto add(const uint256& x, const uint256& y) noexcept
{
    return x + y;
}

auto sub(const uint256& x, const uint256& y) noexcept
{
    return x - y;
}

auto add(const uint512& x, const uint512& y) noexcept
{
    return x + y;
}

auto sub(const uint512& x, const uint512& y) noexcept
{
    return x - y;
}
