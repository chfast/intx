// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/intx.hpp>

namespace
{
struct arithmetic_test_case
{
    intx::uint256 x;
    intx::uint256 y;
    intx::uint256 sum;
    intx::uint256 product;
};

arithmetic_test_case arithmetic_test_cases[] = {
    {0, 0, 0, 0},
    {127, 1, 128, 127},
    {0xffffffffffffffff, 1, intx::uint128{1, 0}, 0xffffffffffffffff},
    {intx::uint128{0x8000000000000000, 0}, intx::uint128{0x8000000000000000, 0},
        intx::uint256{{0, 1}, {0, 0}}, intx::uint256{{0x4000000000000000, 0}, {0, 0}}},
    {intx::uint256{{0, 1}, {0, 0}}, 0, intx::uint256{{0, 1}, {0, 0}}, 0},
    {intx::uint256{{0, 0x8000000000000000}, {0, 0}}, intx::uint256{{0, 0xffffffffffffffff}, {0, 0}},
        intx::uint256{{1, 0x7fffffffffffffff}, {0, 0}}, 0},
    {intx::uint256{{0x7fffffffffffffff, 0}, {0, 0}}, intx::uint256{{0x7fffffffffffffff, 0}, {0, 0}},
        intx::uint256{{0xfffffffffffffffe, 0}, {0, 0}}, 0},
    {intx::uint256{{0x8000000000000000, 0}, {0, 0}}, intx::uint256{{0x7fffffffffffffff, 0}, {0, 0}},
        intx::uint256{{0xffffffffffffffff, 0}, {0, 0}}, 0},
    {intx::uint256{{0xfffffffffffffffe, 0}, {0, 0}}, intx::uint256{{1, 0}, {0, 0}},
        intx::uint256{{0xffffffffffffffff, 0}, {0, 0}}, 0},
    {intx::uint256{{0xffffffffffffffff, 0}, {0, 0}}, intx::uint256{{1, 0}, {0, 0}},
        intx::uint256{{0, 0}, {0, 0}}, 0},
    {intx::uint256{{0xffffffffffffffff, 1}, {0, 0}}, intx::uint256{{0, 0xffffffffffffffff}, {0, 0}},
        intx::uint256{{0, 0}, {0, 0}}, 0},
    {intx::uint256{{0xfffffffffffffffe, 1}, {0, 0}}, intx::uint256{{1, 0xffffffffffffffff}, {0, 0}},
        intx::uint256{{0, 0}, {0, 0}}, 0},
    {intx::uint256{{0xffffffffffffffff, 0}, {0xffffffffffffffff, 0}},
        intx::uint256{{0, 0xffffffffffffffff}, {1, 0}}, intx::uint256{{0, 0}, {0, 0}},
        intx::uint256{{1, 0xffffffffffffffff}, {0, 0}}},
    {intx::uint256{{0xfffffffffffffffe, 1}, {0xfffffffffffffffe, 2}},
        intx::uint256{{1, 0xfffffffffffffffe}, {1, 0xfffffffffffffffe}},
        intx::uint256{{0, 0}, {0, 0}},
        intx::uint256{{0xf, 0xfffffffffffffff4}, {7, 0xfffffffffffffffc}}},
};
}  // namespace
