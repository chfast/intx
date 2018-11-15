// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

/// @file
/// This file provides implementations of full multiplication 64 x 64 -> 128.

#include <stdint.h>

#if defined(__SIZEOF_INT128__)
#define INTX_HAVE_MULL_FULL_64_NATIVE 1

inline uint64_t mul_full_64_native(uint64_t x, uint64_t y, uint64_t* hi)
{
    unsigned __int128 p = (unsigned __int128)x * y;
    *hi = (uint64_t)(p >> 64);
    return (uint64_t)p;
}

#elif defined(_MSC_VER)
#define INTX_HAVE_MULL_FULL_64_NATIVE 1

#include <intrin.h>
inline uint64_t mul_full_64_native(uint64_t x, uint64_t y, uint64_t* hi)
{
    __int64 h;
    __int64 l = _mul128(x, y, &h);
    *hi = h;
    return l;
}

#else
#define INTX_HAVE_MULL_FULL_64_NATIVE 0
#endif

/// Generic and portable implementation of full 64 x 64 -> 128 multiplication
/// by fallback to four 32 x 32 -> 64 multiplications.
inline uint64_t mul_full_64_generic(uint64_t x, uint64_t y, uint64_t* hi)
{
    uint64_t xl = x & 0xffffffff;
    uint64_t xh = x >> 32;
    uint64_t yl = y & 0xffffffff;
    uint64_t yh = y >> 32;

    uint64_t t = xl * yl;
    uint64_t l = t & 0xffffffff;
    uint64_t h = t >> 32;

    t = xh * yl;
    t += h;
    h = t >> 32;

    t = xl * yh + (t & 0xffffffff);
    l |= t << 32;
    *hi = xh * yh + h + (t >> 32);
    return l;
}

inline uint64_t mul_full_64(uint64_t x, uint64_t y, uint64_t* hi)
{
#if INTX_HAVE_MULL_FULL_64_NATIVE
    return mul_full_64_native(x, y, hi);
#else
    return mul_full_64_generic(x, y, hi);
#endif
}
