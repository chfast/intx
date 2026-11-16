// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

// Checks the diagnostics for code using intx with clang -verify. Each expected diagnostic is
// declared in a comment on its line, and any other diagnostic fails the test.
// The TODO cases pin the current behavior that should change.

#include <intx/intx.hpp>

using namespace intx;

enum unscoped_enum
{
    ONE = 1
};

void assign_signed(uint256& x, int a)
{
    x = a;  // expected-warning {{changes signedness}}
}

void assign_floating(uint256& x, double a)
{
    x = a;  // expected-warning {{turns floating-point number into integer}}
}

uint256 construct_signed(int a)
{
    // TODO: Negative values convert modulo 2^64 instead of 2^256, without a warning.
    return a;
}

uint256 construct_floating(double a)
{
    // TODO: Reject floating-point values.
    return a;
}

#if INTX_HAS_BUILTIN_INT128
void assign_int128(uint256& x, builtin_int128 a)
{
    // TODO: Keep all 128 bits.
    x = a;  // expected-warning {{loses integer precision}}
}

uint256 construct_int128(builtin_int128 a)
{
    // TODO: Keep all 128 bits.
    return a;
}

builtin_int128 convert_to_int128(const uint128& x)
{
    // TODO: Keep all 128 bits.
    return static_cast<builtin_int128>(x);
}
#endif

uint256 shift_by_int(const uint256& x, int s)
{
    return x << s;
}

uint256 shift_by_floating(const uint256& x, double s)
{
    // TODO: Reject floating-point shift amounts.
    return x << s;  // expected-warning {{turns floating-point number into integer}}
}

void shift_assign_by_floating(uint256& x, double s)
{
    // TODO: Reject floating-point shift amounts.
    x <<= s;
}

uint256 shift_by_enum(const uint256& x)
{
    // TODO: Reject enum shift amounts.
    return x >> ONE;
}

// TODO: Reject negative shift amounts.
static_assert((uint256{1} << -1) == 0);
static_assert([] {
    auto x = uint256{1};
    x <<= -1;
    return x;
}() == 0);

// TODO: Keep the type of the shifted value.
static_assert(std::same_as<decltype(uint128{1} << uint256{128}), uint256>);
