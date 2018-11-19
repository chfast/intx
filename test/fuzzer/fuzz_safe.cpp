// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <cstring>
#include <intx/safe.hpp>

using namespace intx;

enum class op
{
    add,
    mul,
    div,
    rem,
};

inline void expect(bool condition) noexcept
{
    if (!condition)
        __builtin_trap();
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
{
    safe<int> a, b;

    if (size != 2 * sizeof(a) + 1)
        return 0;

    int i;
    std::memcpy(&i, &data[1], sizeof(i));
    i = __builtin_bswap32(i);
    a = i;
    std::memcpy(&i, &data[1 + sizeof(i)], sizeof(i));
    i = __builtin_bswap32(i);
    b = i;

    int64_t x = a.value();
    int64_t y = b.value();
    int64_t z;

    safe<int> s;
    switch (op(data[0]))
    {
    case op::add:
        s = a + b;
        z = x + y;
        break;

    // case op::mul:
    //     // s = a * b;
    //     // z = x * y;
    //     break;

    // case op::div:
    //     // s = a / b;
    //     // z = y != 0 ? x / y : -1;
    //     break;

    // case op::rem:
    //     // s = a % b;
    //     // z = y != 0 ? x % y : -1;
    //     break;

    default:
        return 0;
    }

    switch (s.get_status())
    {
    case status::normal:
        expect(s == z);
        break;
    case status::plus_infinity:
        expect(z > s.max_value);
        break;
    case status::minus_infinity:
        expect(z < s.min_value);
        break;
    default:
        expect(false);
    }

    return 0;
}
