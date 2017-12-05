#include <cstdint>


struct uint128
{
  uint64_t lo = 0;
  uint64_t hi = 0;
};

using i64 = uint64_t;

#ifndef _MSC_VER
using i128 = unsigned __int128;

void mul_full64_int128(i64* oh, i64* ol, i64 a, i64 b)
{
	auto p = static_cast<i128>(a) * b;
	*oh = static_cast<i64>(p >> 64);
	*ol = static_cast<i64>(p);
}
#else

#include <intrin.h>
void mul_full64_msvc(i64* oh, i64* ol, i64 a, i64 b)
{
	__int64 h;
	__int64 l = _mul128(a, b, &h);
	*ol = static_cast<i64>(l);
	*oh = static_cast<i64>(h);
}

#endif

void mul_full64_portable1(i64* oh, i64* ol, i64 a, i64 b)
{
	i64 al = a & 0xffffffff;
	i64 ah = a >> 32;
	i64 bl = b & 0xffffffff;
	i64 bh = b >> 32;

	i64 t = al * bl;
	i64 u = ah * bl;
	i64 v = al * bh;
	i64 w = ah * bh;

	i64 uh = u >> 32;
	i64 vh = v >> 32;

	i64 m = t + (u << 32);
	bool carry1 = m < t;

	i64 lo = m + (v << 32);
	bool carry2 = lo < m;

	uint64_t hi = uh + vh + w + carry1 + carry2;

	*ol = lo;
	*oh = hi;
}

/// Hacker's Delight version.
void mul_full64_portable2(uint64_t* oh, uint64_t* ol, uint64_t a, uint64_t b)
{
	uint64_t al = a & 0xffffffff;
	uint64_t ah = a >> 32;
	uint64_t bl = b & 0xffffffff;
	uint64_t bh = b >> 32;

	uint64_t t, lo, hi;

	t = al * bl;
	lo = t & 0xffffffff;
    hi = t >> 32;
	t = ah * bl;
    t += hi;
	hi = t >> 32;

	t = al * bh + (t & 0xffffffff);
	lo |= t << 32;
	hi = ah * bh + hi + (t >> 32);

	*ol = lo;
	*oh = hi;
}

constexpr auto mul_full64 = mul_full64_int128;

void add_to(uint128& a, uint64_t b)
{
    a.lo += b;
    a.hi += (a.lo < b);
}

uint128 mul(uint128 a, uint128 b)
{
    uint128 t, p;

    mul_full64(&t.hi, &t.lo, a.lo, b.lo);
    p.lo = t.lo;
    auto hi = t.hi;
    mul_full64(&t.hi, &t.lo, a.hi, b.lo);
    add_to(t, hi);

    auto lo = t.lo;
    mul_full64(&t.hi, &t.lo, a.lo, b.hi);
    add_to(t, lo);

    p.hi = t.lo;

    return p;
}

i128 mul(i128 a, i128 b)
{
    return a * b;
}