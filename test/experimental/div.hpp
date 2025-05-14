
#pragma once
#include <intx/intx.hpp>

namespace intx
{
inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    const auto u = uint128{~uint64_t{0}, ~d};
    uint64_t v{};

#if __x86_64__
    uint64_t _{};
    asm("divq %4" : "=d"(_), "=a"(v) : "d"(u[1]), "a"(u[0]), "g"(d));  // NOLINT(hicpp-no-assembler)
#else
    v = (u / d)[0];
#endif

    return v;
}
}  // namespace intx
