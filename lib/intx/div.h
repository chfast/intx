
#include <climits>
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
    return std::make_tuple(q, r);
}

std::tuple<uint64_t, uint64_t> udivrem_long_gcc(unsigned __int128 x, uint64_t y)
{
    auto q = static_cast<uint64_t>(x / y);
    auto r = static_cast<uint64_t>(x % y);
    return std::make_tuple(q, r);
};

union utwords
{
    unsigned __int128 all;
    struct {
        uint64_t low;
        uint64_t high;
    }s;
};

unsigned __int128 udivmodti4(unsigned __int128 a, unsigned __int128 b, unsigned __int128* rem)
{
    using du_int = uint64_t;
    using tu_int = unsigned __int128;
    const unsigned n_udword_bits = sizeof(du_int) * CHAR_BIT;
    const unsigned n_utword_bits = sizeof(tu_int) * CHAR_BIT;
    utwords n;
    n.all = a;
    utwords d;
    d.all = b;
    utwords q;
    utwords r;
    unsigned sr;
    /* special cases, X is unknown, K != 0 */
    if (n.s.high == 0)
    {
        if (d.s.high == 0)
        {
            /* 0 X
             * ---
             * 0 X
             */
            if (rem)
                *rem = n.s.low % d.s.low;
            return n.s.low / d.s.low;
        }
        /* 0 X
         * ---
         * K X
         */
        if (rem)
            *rem = n.s.low;
        return 0;
    }
    /* n.s.high != 0 */
    if (d.s.low == 0)
    {
        if (d.s.high == 0)
        {
            /* K X
             * ---
             * 0 0
             */
            if (rem)
                *rem = n.s.high % d.s.low;
            return n.s.high / d.s.low;
        }
        /* d.s.high != 0 */
        if (n.s.low == 0)
        {
            /* K 0
             * ---
             * K 0
             */
            if (rem)
            {
                r.s.high = n.s.high % d.s.high;
                r.s.low = 0;
                *rem = r.all;
            }
            return n.s.high / d.s.high;
        }
        /* K K
         * ---
         * K 0
         */
        if ((d.s.high & (d.s.high - 1)) == 0) /* if d is a power of 2 */
        {
            if (rem)
            {
                r.s.low = n.s.low;
                r.s.high = n.s.high & (d.s.high - 1);
                *rem = r.all;
            }
            return n.s.high >> __builtin_ctzll(d.s.high);
        }
        /* K K
         * ---
         * K 0
         */
        sr = __builtin_clzll(d.s.high) - __builtin_clzll(n.s.high);
        /* 0 <= sr <= n_udword_bits - 2 or sr large */
        if (sr > n_udword_bits - 2)
        {
            if (rem)
                *rem = n.all;
            return 0;
        }
        ++sr;
        /* 1 <= sr <= n_udword_bits - 1 */
        /* q.all = n.all << (n_utword_bits - sr); */
        q.s.low = 0;
        q.s.high = n.s.low << (n_udword_bits - sr);
        /* r.all = n.all >> sr; */
        r.s.high = n.s.high >> sr;
        r.s.low = (n.s.high << (n_udword_bits - sr)) | (n.s.low >> sr);
    }
    else /* d.s.low != 0 */
    {
        if (d.s.high == 0)
        {
            /* K X
             * ---
             * 0 K
             */
            if ((d.s.low & (d.s.low - 1)) == 0) /* if d is a power of 2 */
            {
                if (rem)
                    *rem = n.s.low & (d.s.low - 1);
                if (d.s.low == 1)
                    return n.all;
                sr = __builtin_ctzll(d.s.low);
                q.s.high = n.s.high >> sr;
                q.s.low = (n.s.high << (n_udword_bits - sr)) | (n.s.low >> sr);
                return q.all;
            }
            /* K X
             * ---
             * 0 K
             */
            sr = 1 + n_udword_bits + __builtin_clzll(d.s.low) - __builtin_clzll(n.s.high);
            /* 2 <= sr <= n_utword_bits - 1
             * q.all = n.all << (n_utword_bits - sr);
             * r.all = n.all >> sr;
             */
            if (sr == n_udword_bits)
            {
                q.s.low = 0;
                q.s.high = n.s.low;
                r.s.high = 0;
                r.s.low = n.s.high;
            }
            else if (sr < n_udword_bits)  // 2 <= sr <= n_udword_bits - 1
            {
                q.s.low = 0;
                q.s.high = n.s.low << (n_udword_bits - sr);
                r.s.high = n.s.high >> sr;
                r.s.low = (n.s.high << (n_udword_bits - sr)) | (n.s.low >> sr);
            }
            else  // n_udword_bits + 1 <= sr <= n_utword_bits - 1
            {
                q.s.low = n.s.low << (n_utword_bits - sr);
                q.s.high = (n.s.high << (n_utword_bits - sr)) | (n.s.low >> (sr - n_udword_bits));
                r.s.high = 0;
                r.s.low = n.s.high >> (sr - n_udword_bits);
            }
        }
        else
        {
            /* K X
             * ---
             * K K
             */
            sr = __builtin_clzll(d.s.high) - __builtin_clzll(n.s.high);
            /*0 <= sr <= n_udword_bits - 1 or sr large */
            if (sr > n_udword_bits - 1)
            {
                if (rem)
                    *rem = n.all;
                return 0;
            }
            ++sr;
            /* 1 <= sr <= n_udword_bits
             * q.all = n.all << (n_utword_bits - sr);
             * r.all = n.all >> sr;
             */
            q.s.low = 0;
            if (sr == n_udword_bits)
            {
                q.s.high = n.s.low;
                r.s.high = 0;
                r.s.low = n.s.high;
            }
            else
            {
                r.s.high = n.s.high >> sr;
                r.s.low = (n.s.high << (n_udword_bits - sr)) | (n.s.low >> sr);
                q.s.high = n.s.low << (n_udword_bits - sr);
            }
        }
    }
    /* Not a special case
     * q and r are initialized with:
     * q.all = n.all << (n_utword_bits - sr);
     * r.all = n.all >> sr;
     * 1 <= sr <= n_utword_bits - 1
     */
    unsigned carry = 0;
    for (; sr > 0; --sr)
    {
        /* r:q = ((r:q)  << 1) | carry */
        r.s.high = (r.s.high << 1) | (r.s.low >> (n_udword_bits - 1));
        r.s.low = (r.s.low << 1) | (q.s.high >> (n_udword_bits - 1));
        q.s.high = (q.s.high << 1) | (q.s.low >> (n_udword_bits - 1));
        q.s.low = (q.s.low << 1) | carry;
        /* carry = 0;
         * if (r.all >= d.all)
         * {
         *     r.all -= d.all;
         *      carry = 1;
         * }
         */
        const __int128 s = (__int128)(d.all - r.all - 1) >> (n_utword_bits - 1);
        carry = s & 1;
        r.all -= d.all & s;
    }
    q.all = (q.all << 1) | carry;
    if (rem)
        *rem = r.all;
    return q.all;
}

std::tuple<uint64_t, uint64_t> udivrem_long_rt(unsigned __int128 x, uint64_t y)
{
    unsigned __int128 q, r;
    q = udivmodti4(x, y, &r);
    return std::make_tuple(static_cast<uint64_t>(q), static_cast<uint64_t>(r));
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