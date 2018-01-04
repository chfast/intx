
#include <cstdint>
#include <tuple>

inline int clz(uint64_t x)
{
    return __builtin_clzl(x);
}

inline uint64_t umulh(uint64_t x, uint64_t y)
{
    unsigned __int128 p = static_cast<unsigned __int128>(x) * y;
    return static_cast<uint64_t>(p >> 64);
}

uint64_t soft_div_unr_unrolled(uint64_t x, uint64_t y)
{
    // decent start
    uint64_t z = uint64_t(1) << clz(y);

    // z recurrence, 6 iterations (TODO: make sure 6 is enough)
    uint64_t my = 0 - y;
    for (int i = 0; i < 6; ++i)
        z += umulh(z, my * z);

    // q estimate
    uint64_t q = umulh(x, z);
    uint64_t r = x - (y * q);

    // q refinement
    if (r >= y)
    {
        r -= y;
        q += 1;

        if (r >= y)
        {
            r -= y;
            q += 1;
        }
    }
    return q;
}

uint64_t soft_div_unr(uint64_t x, uint64_t y)
{
    // decent start
    uint64_t z = uint64_t(1) << clz(y);

    // z recurrence
    uint64_t my = 0 - y;
    for (int i = 0; i < 6; ++i)
    {
        uint64_t zd = umulh(z, my * z);
        if (zd == 0)
            break;
        z = z + zd;
    }

    // q estimate
    uint64_t q = umulh(x, z);
    uint64_t r = x - (y * q);
    // q refinement
    if (r >= y)
    {
        r = r - y;
        q = q + 1;
        if (r >= y)
        {
            r = r - y;
            q = q + 1;
        }
    }
    return q;
}

std::tuple<uint64_t, uint64_t> udivrem_long_unr(unsigned __int128 x, uint64_t y)
{
    // decent start
    unsigned __int128 z = uint64_t(1) << clz(y);

    // z recurrence
    uint64_t my = 0 - y;
    for (int i = 0; i < 20; ++i)
    {
        auto zd = z * my * z;
        if (zd == 0)
            break;
        z = z + zd;
    }

    // q estimate
    auto p = x * z;
    uint64_t q = static_cast<uint64_t>(p >> 64);
    uint64_t r = static_cast<uint64_t>(x - (y * q));
    // q refinement
    if (r >= y)
    {
        r = r - y;
        q = q + 1;
        if (r >= y)
        {
            r = r - y;
            q = q + 1;
        }
    }
    return {q, r};
}

std::tuple<uint64_t, uint64_t> udivrem_long_gcc(unsigned __int128 x, uint64_t y)
{
    auto q = static_cast<uint64_t>(x / y);
    auto r = static_cast<uint64_t>(x % y);
    return {q, r};
};

uint64_t soft_div_shift(uint64_t x, uint64_t y)
{
    uint64_t r = x;
    uint64_t q = 0;
    uint64_t y0 = y;  // original divisor

    // divisor doubling phase
    if (x >= y)
    {
        x = x - y;
        while (x >= y)
        {
            x = x - y;
            y = y + y;
        }
    }

    // quotient computing phase
    for (;;)
    {
        if (r >= y)
        {
            r = r - y;
            q = q + 1;
        }
        if (y == y0)
            break;
        q = q + q;
        y = y >> 1;
    }

    return q;
}

uint64_t soft_div_improved_shift(uint64_t x, uint64_t y)
{
    uint64_t r = x, q = 0;
    if (y <= r)
    {
        unsigned i = __builtin_clzl(y) - __builtin_clzl(r);
        y = y << i;
        // quotient computing phase
        for (;;)
        {
            if (r >= y)
            {
                r = r - y;
                q = q + 1;
            }
            if (i == 0)
                break;
            i = i - 1;
            q = q + q;
            y = y >> 1;
        }
    }
    return q;
}

// uint64_t soft_div_unr_bitrev(uint64_t x, uint64_t y)
//{
//    uint64_t q, r;
//// decent start
//    uint64_t yr = bitrev(y);
//    uint64_t z = band(yr,0-yr);
//// z recurrence
//    uint64_t my = 0-y;
//    for (;;) {
//        uint64_t zd = umulh(z,mul(my,z));
//        if (zd == 0) break;
//        z = z + zd;
//    }
//// q estimate
//    q = umulh(x,z); r = x - mul(y,q);
//// q refinement
//    if (r >= y) { r = r - y; q = q + 1;
//        if (r >= y) { r = r - y; q = q + 1; }
//    }
//    return q;
//}