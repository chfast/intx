#pragma once

#include <cstdint>
#include <array>
#include <limits>
#include <tuple>

struct uint256
{
	std::array<uint64_t, 4> limbs = {{0, 0, 0, 0}};

	constexpr uint256() = default;

	uint256(uint64_t i)
	{
		limbs[0] = i;
	}
};

struct uint128
{
	uint64_t lo = 0;
	uint64_t hi = 0;
};

unsigned __int128 add(unsigned __int128 a, unsigned __int128 b)
{
	return a + b;
}

uint64_t add2(uint64_t ah, uint64_t al, uint64_t bh, uint64_t bl)
{
	(void)ah;
	auto l = al + bl;
	auto c = l < al;
	auto h = bh + bl + c;
	return h;
}

void add_128(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	// Intermediate values are used to avoid memory aliasing issues.
	auto l = a[0] + b[0];
	auto c = l < a[0];
	auto h = a[1] + b[1] + c;
	r[0] = l;
	r[1] = h;
}

bool adc_128(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	// Intermediate values are used to avoid memory aliasing issues.
	auto l = a[0] + b[0];
	auto c = l < a[0];
	auto h = a[1] + b[1];
	auto c1 = h < a[1];
	h += c;
	auto c2 = h < c;


	r[0] = l;
	r[1] = h;
	return c1 | c2;
}

void add_128(uint64_t* r, const uint64_t* a, uint64_t b)
{
	auto l = a[0] + b;
	auto c = l < a[0];
	auto h = a[1] + c;
	r[0] = l;
	r[1] = h;  // TODO: Do not store if not needed.
}

bool lt_128(const uint64_t* a, const uint64_t* b)
{
	if (a[1] < b[1])
		return true;
	return a[0] < b[0];
}

void add_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	uint64_t l[2];
	add_128(l, a, b);
	auto c = lt_128(a, b);
	uint64_t h[2];
	add_128(h, a + 2, b + 2);
	add_128(h, h, c);
	r[0] = l[0];
	r[1] = l[1];
	r[2] = h[0];
	r[3] = h[1];
}

void add2_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	uint64_t l[2];
	auto c = adc_128(l, a, b);
	uint64_t h[2];
	add_128(h, a + 2, b + 2);
	add_128(h, h, c);
	r[0] = l[0];
	r[1] = l[1];
	r[2] = h[0];
	r[3] = h[1];
}

bool add3_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	uint64_t l[4];
	bool c = 0;

	for (int i = 0; i < 4; ++i)
	{
		l[i] = a[i] + c;
		c = l[i] < c;

		l[i] += b[i];
		c |= l[i] < b[i];
	}

	r[0] = l[0];
	r[1] = l[1];
	r[2] = l[2];
	r[3] = l[3];
	return c;
}

void add_no_carry_256(uint64_t* r, const uint64_t* a, const uint64_t* b)
{
	add3_256(r, a, b);
}

uint256 operator+(uint256 a, uint256 b)
{
	uint256 r;
	add_no_carry_256(r.limbs.data(), a.limbs.data(), b.limbs.data());
	return r;
}

bool operator==(uint256 a, uint256 b)
{
	return std::equal(a.limbs.begin(), a.limbs.end(), b.limbs.begin());
}


using u128 = unsigned __int128;

struct u256
{
	using half = u128;

	half lo = 0;
	half hi = 0;
};

bool operator<(u256 a, u256 b)
{
	if (a.hi == b.hi)
		return a.lo < b.lo;
	return a.hi < b.hi;
}

std::tuple<u128, bool> add_with_carry(u128 a, u128 b)
{
	auto s = a + b;
	auto k = s < a;
	return {s, k};
}

std::tuple<u256, bool> add_with_carry(u256 a, u256 b)
{
	u256 s;
	bool k1, k2, k3;
	std::tie(s.lo, k1) = add_with_carry(a.lo, b.lo);
	std::tie(s.hi, k2) = add_with_carry(a.hi, b.hi);
	std::tie(s.hi, k3) = add_with_carry(s.hi, k1);
	return {s, k2 || k3};
}

u256 add(u256 a, u256 b)
{
	return std::get<0>(add_with_carry(a, b));
}

unsigned clz(uint64_t a)
{
	return __builtin_clzl(a);
}

unsigned clz2(uint64_t a)
{
	unsigned c = 0;
	for (; c < 64; ++c)
	{
		if ((a & 0x8000000000000000) != 0)
			break;
		a <<= 1;
	}
	return c;
}

u256 operator+(u256 a, u256 b)
{
	u256 s;
	s.lo = a.lo + b.lo;
	auto k = s.lo < a.lo;
	s.hi = a.hi + b.hi + k;
	return s;
}

bool operator==(u256 a, u256 b)
{
	return a.lo == b.lo && a.hi == b.hi;
}