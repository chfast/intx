// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "../utils/gmp.hpp"
#include <intx/intx.hpp>
#include <cstring>

constexpr size_t input_size = 3 * sizeof(intx::uint256);

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
    if (data_size < input_size)
        return 0;

    intx::uint256 a, b, m;
    std::memcpy(&a, &data[0], sizeof(a));
    std::memcpy(&b, &data[sizeof(a)], sizeof(b));
    std::memcpy(&m, &data[sizeof(a) + sizeof(b)], sizeof(m));

    if (m == 0)
        return 0;

    const auto r = intx::addmod(a, b, m);
    const auto e = intx::gmp::addmod(a, b, m);

    if (r != e)
        __builtin_trap();

    return 0;
}
