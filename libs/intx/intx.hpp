#pragma once

#include <cstdint>
#include <array>
#include <limits>

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