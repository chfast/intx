// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <cstdint>

inline uint64_t udiv_long(uint64_t uh, uint64_t ul, uint64_t v) noexcept
{
    // RDX:RAX by r/m64 : RAX <- Quotient, RDX <- Remainder.
    uint64_t q, r;
    asm("divq %4" : "=d"(r), "=a"(q) : "d"(uh), "a"(ul), "g"(v));
    return q;
}

inline uint64_t reciprocal_naive(uint64_t d) noexcept
{
    return udiv_long(~d, ~uint64_t(0), d);
}
