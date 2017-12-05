#include <mul.h>

#include <gtest/gtest.h>

auto mul_full64_optimized = mul_full64_int128;

constexpr uint64_t edges[] = {
    0x0000000000000000,
    0x0000000000000001,
    0x0000000000000002,
    0x000000000000000f,
    0x0000000000000010,
    0x00000000fffffffe,
    0x00000000ffffffff,
    0x0000000100000000,
    0x0000000100000001,
    0x00000001fffffffe,
    0x00000001ffffffff,
    0x0000000200000000,
    0x0000000200000001,
    0x0fffffffffffffff,
    0x1000000000000000,
    0x1000000000000001,
    0x1010101010101010,
    0x1ffffffffffffffe,
    0x1fffffffffffffff,
    0x2000000000000000,
    0x7000000000000000,
    0x7ffffffffffffffd,
    0x7ffffffffffffffe,
    0x7fffffffffffffff,
    0x8000000000000000,
    0x8000000000000001,
    0xfffffffffffffffd,
    0xfffffffffffffffe,
    0xffffffffffffffff,
};

TEST(mul, mul_full64_edges)
{
	for (auto a : edges)
	{
		for (auto b : edges)
		{
			uint64_t p1h, p1l, p2h, p2l, p3h, p3l;
			mul_full64_portable1(&p1h, &p1l, a, b);
			mul_full64_portable2(&p2h, &p2l, a, b);
			mul_full64_optimized(&p3h, &p3l, a, b);
			EXPECT_EQ(p1l, p3l) << "lo(" << a << " * " << b << ")";
			EXPECT_EQ(p1h, p3h) << "hi(" << a << " * " << b << ")";
			EXPECT_EQ(p2l, p3l) << "lo(" << a << " * " << b << ")";
			EXPECT_EQ(p2h, p3h) << "hi(" << a << " * " << b << ")";
		}
	}
}

TEST(mul, mul128)
{
    for (auto al: edges)
    {
        for (auto ah: edges)
        {
            for (auto bl: edges)
            {
                for (auto bh: edges)
                {
                    uint128 a, b;
                    a.lo = al;
                    a.hi = ah;
                    b.lo = bl;
                    b.hi = bh;

                    unsigned __int128 c, d;
                    c = ah;
                    c <<= 64;
                    c |= al;
                    d = bh;
                    d <<= 64;
                    d |= bl;

                    auto p = mul(a, b);
                    auto q = mul(c, d);

                    auto ql = static_cast<uint64_t>(q);
                    auto qh = static_cast<uint64_t>(q >> 64);
                    ASSERT_EQ(p.lo, ql) << "lo( (" << ah << "," << al << ") * (" << bh << "," << bl << ") )";
                    ASSERT_EQ(p.hi, qh) << "lo( (" << ah << "," << al << ") * (" << bh << "," << bl << ") )";
                }
            }
        }
    }
}