
#pragma once
#include <intx/intx.hpp>

namespace intx
{
/// Computes the reciprocal with the intx uint128 division.
inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    return (uint128{~uint64_t{0}, ~d} / d)[0];
}

/// Computes the reciprocal with the x86-64 128/64 division instruction (divq).
inline uint64_t reciprocal_native(uint64_t d) noexcept
{
#ifdef __x86_64__
    uint64_t _;    // NOLINT(*-init-variables)
    uint64_t v;    // NOLINT(*-init-variables)
    asm("divq %4"  // NOLINT(*-no-assembler)
        : "=d"(_), "=a"(v)
        : "d"(~d), "a"(~uint64_t{0}), "r"(d));
    return v;
#else
    return reciprocal_naive(d);
#endif
}

/// Computes the reciprocal with the compiler's builtin 128-bit division.
inline uint64_t reciprocal_builtin_uint128(uint64_t d) noexcept
{
#if INTX_HAS_BUILTIN_INT128
    const auto u = (builtin_uint128{~d} << 64) | ~uint64_t{0};
    return static_cast<uint64_t>(u / d);
#else
    return reciprocal_naive(d);
#endif
}

/// Computes the reciprocal with two hardware 64-bit divisions (Hacker's Delight "divlu").
///
/// This is the "native" variant for architectures without a 128/64 division instruction
/// (e.g. AArch64 where udiv is 64/64 only).
inline uint64_t reciprocal_udiv(uint64_t d) noexcept
{
    INTX_REQUIRE(d & 0x8000000000000000);  // Must be normalized.

    constexpr uint64_t b = uint64_t{1} << 32;
    constexpr uint64_t mask = b - 1;

    // Dividend: u = (~d : ~0). Because d is normalized, ~d < d so the quotient fits in 64 bits.
    const uint64_t un32 = ~d;
    const uint64_t un1 = mask;
    const uint64_t un0 = mask;
    const uint64_t dn1 = d >> 32;
    const uint64_t dn0 = d & mask;

    uint64_t q1 = un32 / dn1;
    uint64_t rhat = un32 - q1 * dn1;
    while (q1 >= b || q1 * dn0 > ((rhat << 32) | un1))
    {
        --q1;
        rhat += dn1;
        if (rhat >= b)
            break;
    }

    const uint64_t un21 = (un32 << 32) + un1 - q1 * d;

    uint64_t q0 = un21 / dn1;
    rhat = un21 - q0 * dn1;
    while (q0 >= b || q0 * dn0 > ((rhat << 32) | un0))
    {
        --q0;
        rhat += dn1;
        if (rhat >= b)
            break;
    }

    return (q1 << 32) + q0;
}

/// The copy of the GMP algorithm from "Improved division by invariant integers".
constexpr uint64_t reciprocal_gmp(uint64_t d) noexcept
{
    INTX_REQUIRE(d & 0x8000000000000000);  // Must be normalized.

    const uint64_t d9 = d >> 55;
    const uint32_t v0 = internal::reciprocal_table[static_cast<size_t>(d9 - 256)];

    const uint64_t d40 = (d >> 24) + 1;
    const uint64_t v1 = (v0 << 11) - uint32_t(uint32_t{v0 * v0} * d40 >> 40) - 1;

    const uint64_t v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);

    const uint64_t d0 = d & 1;
    const uint64_t d63 = (d >> 1) + d0;  // ceil(d/2)
    const uint64_t e = ((v2 >> 1) & (0 - d0)) - (v2 * d63);
    const uint64_t v3 = (umul(v2, e)[1] >> 1) + (v2 << 31);

    const uint64_t v4 = v3 - (umul(v3, d) + d)[1] - d;
    return v4;
}
}  // namespace intx
