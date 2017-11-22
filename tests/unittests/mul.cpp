
#include <mul.h>

#include <gtest/gtest.h>

auto mul_full64_optimized = mul_full64_int128;

TEST(mul, mul_full64_edges)
{
	uint64_t edges[] = {
		0,
		1,
		2,
		0xf,
		0x10,
		0xfffffffe,
		0xffffffff,
		0x100000000,
		0x1010101010101010,
		0xfffffffffffffffd,
		0xfffffffffffffffe,
		0xffffffffffffffff,
	};

	for (auto a : edges)
	{
		for (auto b : edges)
		{
			i64 p1h, p1l, p2h, p2l;
			mul_full64_portable(&p1h, &p1l, a, b);
			mul_full64_optimized(&p2h, &p2l, a, b);
			ASSERT_EQ(p1l, p2l);
			ASSERT_EQ(p1h, p2h);
		}
	}
}