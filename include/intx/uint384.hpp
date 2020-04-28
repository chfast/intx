// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#pragma once

#include <intx/intx.hpp>

namespace intx
{
struct uint384
{
    static constexpr auto num_words = 6;

    uint64_t words[num_words]{};

    uint384() noexcept = default;

    explicit uint384(uint512 v) noexcept
    {
        for (int i = 0; i < num_words; ++i)
            words[i] = as_words(v)[i];
    }

    operator uint512() const noexcept
    {
        uint512 a;
        for (int i = 0; i < num_words; ++i)
            as_words(a)[i] = words[i];
        return a;
    }
};

inline uint384 operator+(const uint384& x, const uint384& y) noexcept
{
    return static_cast<uint384>(uint512{x} + uint512{y});
}

inline uint384 operator-(const uint384& x, const uint384& y) noexcept
{
    return static_cast<uint384>(uint512{x} - uint512{y});
}

inline uint384 operator*(const uint384& x, const uint384& y) noexcept
{
    return static_cast<uint384>(uint512{x} * uint512{y});
}

inline uint384 operator/(const uint384& x, const uint384& y) noexcept
{
    return static_cast<uint384>(uint512{x} / uint512{y});
}

inline bool operator==(const uint384& x, const uint384& y) noexcept
{
    for (int i = 0; i < uint384::num_words; ++i)
    {
        if (x.words[i] != y.words[i])
            return false;
    }
    return true;
}
}  // namespace intx
