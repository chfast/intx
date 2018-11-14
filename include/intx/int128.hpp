// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <cstdint>

namespace intx
{
struct uint128
{
    uint64_t lo = 0;
    uint64_t hi = 0;

    constexpr uint128() noexcept = default;

    constexpr uint128(uint64_t x) noexcept : lo{x} {}

    constexpr uint128(uint64_t hi, uint64_t lo) noexcept : lo{lo}, hi{hi} {}
};


constexpr bool operator==(const uint128& x, const uint128& y) noexcept
{
    // Bitwise & used to avoid branching.
    return (x.lo == y.lo) & (x.hi == y.hi);
}

constexpr bool operator!=(const uint128& x, const uint128& y) noexcept
{
    return !(x == y);
}

constexpr bool operator<(const uint128& x, const uint128& y) noexcept
{
    // Bitwise operators are used to avoid branching.
    return (x.hi < y.hi) | ((x.hi == y.hi) & (x.lo < y.lo));
}

constexpr bool operator<=(const uint128& x, const uint128& y) noexcept
{
    // Bitwise | used to avoid branching.
    return (x < y) | (x == y);
}

constexpr bool operator>(const uint128& x, const uint128& y) noexcept
{
    return !(x <= y);
}

constexpr bool operator>=(const uint128& x, const uint128& y) noexcept
{
    return !(x < y);
}


constexpr uint128 operator|(const uint128& x, const uint128& y) noexcept
{
    return {x.hi | y.hi, x.lo | y.lo};
}

constexpr uint128 operator&(const uint128& x, const uint128& y) noexcept
{
    return {x.hi & y.hi, x.lo & y.lo};
}

constexpr uint128 operator^(const uint128& x, const uint128& y) noexcept
{
    return {x.hi ^ y.hi, x.lo ^ y.lo};
}

constexpr uint128 operator~(const uint128& x) noexcept
{
    return {~x.hi, ~x.lo};
}


constexpr uint128 operator+(const uint128& x, const uint128& y) noexcept
{
    return {x.hi + y.hi + (x.lo > (x.lo + y.lo)), x.lo + y.lo};
}

constexpr uint128 operator-(const uint128& x) noexcept
{
    return ~x + 1;
}

constexpr uint128 operator-(const uint128& x, const uint128& y) noexcept
{
    return x + -y;
}


}  // namespace intx