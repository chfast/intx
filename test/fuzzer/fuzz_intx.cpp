// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../utils/gmp.hpp"
#include <intx/intx.hpp>
#include <cstring>

using namespace intx;

enum class op : uint8_t
{
    divrem = 0x00,
    mul = 0x01,
    shl = 0x02,
    lsr = 0x03,
    add = 0x04,
    sub = 0x05,
    sdivrem = 0x06,
    cmp = 0x07,
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

    // Load 2 values. BE for easier extracting tests from corpus.
    const auto a = be::unsafe::load<T>(&data[1]);
    const auto b = be::unsafe::load<T>(&data[1 + arg_size]);

    switch (static_cast<op>(data[0]))
    {
    case op::divrem:
        if (b != 0)
        {
            auto x = udivrem(a, b);
            auto y = gmp::udivrem(a, b);
            expect_eq(x.quot, y.quot);
            expect_eq(x.rem, y.rem);
        }
        break;
    case op::sdivrem:
        if (b != 0)
        {
            auto x = sdivrem(a, b);
            auto y = gmp::sdivrem(a, b);
            expect_eq(x.quot, y.quot);
            expect_eq(x.rem, y.rem);
        }
        break;
    case op::mul:
    {
        auto x = a * b;
        auto y = gmp::mul(a, b);
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
    case op::lsr:
    {
        auto x = a >> b;
        auto s = T(1) << b;
        auto y = (s != 0) ? a / s : 0;
        expect_eq(x, y);
        break;
    }
    case op::add:
        expect_eq(a + b, gmp::add(a, b));
        break;

    case op::sub:
    {
        const auto s = a - b;
        expect_eq(s, gmp::sub(a, b));
        expect_eq(s, a + -b);
        expect_eq(s, a + (~b + 1));
        break;
    }
    case op::cmp:
    {
        auto aa = to_big_endian(a);
        auto bb = to_big_endian(b);
        auto m = std::memcmp(&aa, &bb, sizeof(aa));
        expect_eq(a < b, m < 0);
        expect_eq(a <= b, m <= 0);
        expect_eq(a > b, m > 0);
        expect_eq(a >= b, m >= 0);
        expect_eq(a == b, m == 0);
        expect_eq(a != b, m != 0);
        break;
    }

    default:
        break;
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t data_size) noexcept
{
    test_op<intx::uint<4096>>(data, data_size);
    test_op<intx::uint<2048>>(data, data_size);
    test_op<intx::uint<1024>>(data, data_size);
    test_op<intx::uint<512>>(data, data_size);
    test_op<intx::uint<384>>(data, data_size);
    test_op<intx::uint<320>>(data, data_size);
    test_op<intx::uint<256>>(data, data_size);
    test_op<intx::uint<192>>(data, data_size);
    test_op<intx::uint<128>>(data, data_size);
    return 0;
}
