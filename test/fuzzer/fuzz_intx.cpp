// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

#include "../utils/gmp.hpp"
#include <cstring>

using namespace intx;

enum class op : uint8_t
{
    divrem,
    mul,
    shl,
};

template <typename T>
inline void expect_eq(const T& x, const T& y) noexcept
{
    if (x != y)
        __builtin_trap();
}

template <typename T>
inline void test_op(const uint8_t* data, size_t data_size) noexcept
{
    static constexpr auto arg_size = sizeof(T);
    if (data_size != 2 * arg_size + 1)
        return;

    T a, b;
    std::memcpy(&a, &data[1], arg_size);
    std::memcpy(&b, &data[1 + arg_size], arg_size);
    a = bswap(a);  // Bswap for BE - easier to extract the test from corpus.
    b = bswap(b);

    switch (static_cast<op>(data[0]))
    {
    case op::divrem:
        if (b != 0)
        {
            auto x = udivrem(a, b);
            auto y = gmp_udiv_qr(a, b);
            expect_eq(std::get<0>(x), std::get<0>(y));
            expect_eq(std::get<1>(x), std::get<1>(y));
        }
        break;
    case op::mul:
    {
        auto x = a * b;
        auto y = gmp_mul(a, b);
        expect_eq(x, y);
        break;
    }
    case op::shl:
    {
        auto x = a << b;
        auto s = T(1) << b;
        auto y = a * s;
        expect_eq(x, y);
        break;
    }

    default:
        break;
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t data_size) noexcept
{
    test_op<uint512>(data, data_size);
    test_op<uint256>(data, data_size);
    return 0;
}
