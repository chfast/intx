// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include "experiments.hpp"
#include <intx/int128.hpp>

namespace intx
{
namespace experiments
{
namespace
{
constexpr uint16_t reciprocal_table_item(uint8_t d9) noexcept
{
    return uint16_t(0x7fd00 / (0x100 | d9));
}

#define REPEAT4(x)                                                  \
    reciprocal_table_item((x) + 0), reciprocal_table_item((x) + 1), \
        reciprocal_table_item((x) + 2), reciprocal_table_item((x) + 3)

#define REPEAT32(x)                                                                         \
    REPEAT4((x) + 4 * 0), REPEAT4((x) + 4 * 1), REPEAT4((x) + 4 * 2), REPEAT4((x) + 4 * 3), \
        REPEAT4((x) + 4 * 4), REPEAT4((x) + 4 * 5), REPEAT4((x) + 4 * 6), REPEAT4((x) + 4 * 7)

#define REPEAT256()                                                                           \
    REPEAT32(32 * 0), REPEAT32(32 * 1), REPEAT32(32 * 2), REPEAT32(32 * 3), REPEAT32(32 * 4), \
        REPEAT32(32 * 5), REPEAT32(32 * 6), REPEAT32(32 * 7),

constexpr uint16_t reciprocal_table[] = {REPEAT256()};
}  // namespace



/// Computes the reciprocal (2^128 - 1) / d - 2^64 for normalized d.
///
/// Based on Algorithm 2 from "Improved division by invariant integers".
uint64_t reciprocal(uint64_t d) noexcept
{
    using u128 = unsigned __int128;

    auto d0 = d % 2;
    auto d9 = uint8_t(d >> 55);
    auto d40 = (d >> 24) + 1;
    auto d63 = ((d - 1) / 2) + 1;  // ceil(d/2)

    auto v0 = uint64_t{reciprocal_table[d9]};

    auto v1 = (v0 << 11) - (v0 * v0 * d40 >> 40) - 1;

    auto v2 = (v1 << 13) + (v1 * ((uint64_t{1} << 60) - v1 * d40) >> 47);

    auto e = (v2 / 2) * d0 - v2 * d63;
    auto p = uint64_t((u128{v2} * e) >> 64);
    auto v3 = (v2 << 31) + (p >> 1);

    auto b = (v3 + (u128{1} << 64) + 1) * d;
    auto v4 = v3 - uint64_t(b >> 64);

    return v4;
}

}  // namespace experiments
}  // namespace intx