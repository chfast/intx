//#include <mul.h>
#include <intx.hpp>

#include <gtest/gtest.h>
#include <gmp.h>

//auto mul_full64_optimized = mul_full64_int128;

using namespace intx;

constexpr uint64_t maximal[] = {
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

constexpr uint64_t normal[] = {
    0x0000000000000000,
    0x0000000000000001,
    0x000000000000000f,
    0x0000000000000010,
    0x00000000000000ff,
    0x5555555555555555,
    0x7fffffffffffffff,
    0x8000000000000000,
    0x8000000000000001,
    0xaaaaaaaaaaaaaaaa,
    0xeeeeeeeeeeeeeeee,
    0xff00000000000000,
    0xfffffffffffffffe,
    0xffffffffffffffff,
};

constexpr uint64_t minimal[] = {
    0x0000000000000000,
    0x0000000000000001,
    0x5555555555555555,
    0x7fffffffffffffff,
    0x8000000000000000,
    0xaaaaaaaaaaaaaaaa,
    0xfffffffffffffffe,
    0xffffffffffffffff,
};

class Uint256Test : public ::testing::Test {
protected:

    static constexpr size_t limbs = sizeof(uint256) / sizeof(mp_limb_t);

    std::vector<uint256> numbers;


    Uint256Test()
    {
        auto& parts_set = minimal;
        for (auto a : parts_set)
        {
            for (auto b : parts_set)
            {
                for (auto c : parts_set)
                {
                    for (auto d : parts_set)
                    {
                        uint256 n;
                        n.lo = (static_cast<uint128>(a) << 64) | b;
                        n.hi = (static_cast<uint128>(c) << 64) | d;
                        numbers.emplace_back(n);
                    }
                }
            }
        }
    }
};

TEST_F(Uint256Test, add_against_gmp)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            uint256 gmp;
            auto p_gmp = (mp_ptr)&gmp;
            auto p_a = (mp_srcptr)&a;
            auto p_b = (mp_srcptr)&b;
            mpn_add_n(p_gmp, p_a, p_b, limbs);

            auto s = add(a, b);
            EXPECT_EQ(gmp, s);
        }
    }

    std::cerr << (numbers.size() * numbers.size()) << " additions";
}

TEST_F(Uint256Test, add_against_sub)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            uint256 sum = add(a, b);
            uint256 test_a = sub(sum, b);
            uint256 test_b = sub(sum, a);
            EXPECT_EQ(a, test_a);
            EXPECT_EQ(b, test_b);
        }
    }
}

TEST_F(Uint256Test, shift_one_bit)
{
    for (unsigned shift = 0; shift < 256; ++shift)
    {
        uint256 x = 1;
        uint256 y = shl(x, shift);
        uint256 z = lsr(y, shift);
        EXPECT_EQ(x, z) << "shift: " << shift;
    }
}

TEST_F(Uint256Test, not_of_zero)
{
    uint256 ones = bitwise_not(uint256(0));
    for (unsigned pos = 0; pos < 256; ++pos)
    {
        uint256 probe = shl(uint256(1), pos);
        uint256 test = bitwise_and(probe, ones);
        EXPECT_NE(test, 0) << "bit position: " << pos;
    }
}

TEST_F(Uint256Test, shift_all_ones)
{
    for (unsigned shift = 0; shift < 256; ++shift)
    {
        uint256 x = 1;
        uint256 y = shl(x, shift);
        uint256 z = lsr(y, shift);
        EXPECT_EQ(x, z) << "shift: " << shift;
    }
}

TEST(Uint64Test, clz)
{
    for (auto n : maximal)
    {
        auto c = intx::clz(n);
        auto d = intx::generic::clz(n);
        EXPECT_EQ(c, d) << std::hex << n;
    }
}

//TEST(mul, mul_full64_edges)
//{
//	for (auto a : edges)
//	{
//		for (auto b : edges)
//		{
//			uint64_t p1h, p1l, p2h, p2l, p3h, p3l;
//			mul_full64_portable1(&p1h, &p1l, a, b);
//			mul_full64_portable2(&p2h, &p2l, a, b);
//			mul_full64_optimized(&p3h, &p3l, a, b);
//			EXPECT_EQ(p1l, p3l) << "lo(" << a << " * " << b << ")";
//			EXPECT_EQ(p1h, p3h) << "hi(" << a << " * " << b << ")";
//			EXPECT_EQ(p2l, p3l) << "lo(" << a << " * " << b << ")";
//			EXPECT_EQ(p2h, p3h) << "hi(" << a << " * " << b << ")";
//		}
//	}
//}
//
//TEST(mul, mul128)
//{
//    for (auto al: edges)
//    {
//        for (auto ah: edges)
//        {
//            for (auto bl: edges)
//            {
//                for (auto bh: edges)
//                {
//                    uint128 a, b;
//                    a.lo = al;
//                    a.hi = ah;
//                    b.lo = bl;
//                    b.hi = bh;
//
//                    unsigned __int128 c, d;
//                    c = ah;
//                    c <<= 64;
//                    c |= al;
//                    d = bh;
//                    d <<= 64;
//                    d |= bl;
//
//                    auto p = mul(a, b);
//                    auto q = mul(c, d);
//
//                    auto ql = static_cast<uint64_t>(q);
//                    auto qh = static_cast<uint64_t>(q >> 64);
//                    ASSERT_EQ(p.lo, ql) << "lo( (" << ah << "," << al << ") * (" << bh << "," << bl << ") )";
//                    ASSERT_EQ(p.hi, qh) << "lo( (" << ah << "," << al << ") * (" << bh << "," << bl << ") )";
//                }
//            }
//        }
//    }
//}