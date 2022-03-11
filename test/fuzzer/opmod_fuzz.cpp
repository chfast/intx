// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../experimental/addmod.hpp"
#include "../utils/gmp.hpp"
#include <intx/intx.hpp>
#include <cstring>
#include <iostream>

constexpr size_t input_size = 3 * sizeof(intx::uint256);

std::ostream& operator<<(std::ostream& os, const intx::uint256& x)
{
    return os << "0x" << to_string(x, 16);
}

extern "C" size_t LLVMFuzzerMutate(uint8_t* data, size_t size, size_t max_size);

extern "C" size_t LLVMFuzzerCustomMutator(
    uint8_t* data, size_t size, size_t max_size, unsigned int /*seed*/) noexcept
{
    if (max_size >= input_size)
        size = input_size;
    return LLVMFuzzerMutate(data, size, max_size);
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t data_size) noexcept
{
    static constexpr decltype(&intx::addmod) addmod_fns[] = {
        intx::addmod,
        intx::test::addmod_public,
        intx::test::addmod_simple,
        intx::test::addmod_prenormalize,
        intx::test::addmod_daosvik_v1,
        intx::test::addmod_daosvik_v2,
    };

    if (data_size < input_size)
        return 0;

    intx::uint256 a, b, m;
    std::memcpy(&a, &data[0], sizeof(a));
    std::memcpy(&b, &data[sizeof(a)], sizeof(b));
    std::memcpy(&m, &data[sizeof(a) + sizeof(b)], sizeof(m));

    if (m == 0)
        return 0;

    const auto expected = intx::gmp::addmod(a, b, m);
    for (size_t i = 0; i < std::size(addmod_fns); ++i)
    {
        const auto result = addmod_fns[i](a, b, m);

        if (INTX_UNLIKELY(result != expected))
        {
            std::cerr << "FAILED: [" << i << "]\n  " << a << " + " << b << " mod " << m
                      << "\n  result:   " << result << "\n  expected: " << expected << "\n";
            __builtin_trap();
        }
    }

    return 0;
}
