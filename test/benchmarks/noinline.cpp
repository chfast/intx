// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
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

auto exp(const uint256& x, const uint256& y) noexcept
{
    return intx::exp(x, y);
}

auto reciprocal_2by1_noinline(uint64_t d) noexcept
{
    return reciprocal_2by1(d);
}

auto reciprocal_3by2_noinline(uint128 d) noexcept
{
    return reciprocal_3by2(d);
}
