#include <intx/intx.hpp>
#include <intx/gmp.hpp>

#include <gtest/gtest.h>
#include <gmp.h>

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

class Uint256Test : public testing::Test {
protected:

    static constexpr size_t limbs = sizeof(uint256) / sizeof(mp_limb_t);

    std::vector<uint256> numbers;


    Uint256Test()
    {
        auto& parts_set = normal;
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

class Uint256ParamTest : public Uint256Test, public ::testing::WithParamInterface<int>
{};

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

TEST_F(Uint256Test, mul_against_gmp)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            uint256 gmp;
            auto p_gmp = (mp_ptr)&gmp;
            auto p_a = (mp_srcptr)&a;
            auto p_b = (mp_srcptr)&b;
            mpn_mul_n(p_gmp, p_a, p_b, limbs);

            auto p = mul(a, b);
            EXPECT_EQ(gmp, p);
        }
    }
}

TEST_F(Uint256Test, udiv_against_gmp)
{
    for (auto a : numbers)
    {
        for (auto d : numbers)
        {
            if (d == 0)
                continue;

            uint256 q, r, q_gmp, r_gmp;
            std::tie(q, r) = udiv_qr_unr(a, d);
            std::tie(q_gmp, r_gmp) = gmp_udiv_qr(a, d);
            EXPECT_EQ(q, q_gmp) << to_string(a) << " / " << to_string(d) << " = " << to_string(q);
            EXPECT_EQ(r, r_gmp) << to_string(a) << " % " << to_string(d) << " = " << to_string(r);
        }
    }
}

TEST_F(Uint256Test, add_against_sub)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            uint256 sum = add(a, b);
            uint256 test = sub(sum, b);
            EXPECT_EQ(a, test);
        }
    }
}

TEST_F(Uint256Test, simple_udiv)
{
    uint256 a = 0xffffffffffffffff;
    uint256 b = 0xffffffffffffffff;
    uint256 q, r;
    std::tie(q, r) = udiv_qr_unr(mul(a, b), b);
    EXPECT_EQ(q, a);
    EXPECT_EQ(r, 0);
}

TEST_F(Uint256Test, mul_against_div)
{
    for (auto a : numbers)
    {
        for (auto b : numbers)
        {
            if (b == 0)
                continue;
            uint256 h = umul_hi(a, b);
            if (h != 0)  // Overflow.
                continue;
            uint256 prod = mul(a, b);
            uint256 q, r;
            std::tie(q, r) = udiv_qr_unr(prod, b);
            EXPECT_EQ(a, q);
            EXPECT_EQ(r, 0);
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

TEST_F(Uint256Test, clz_one_bit)
{
    uint256 t = 1;
    unsigned b = num_bits(t);
    for (unsigned i = 0; i < b; ++i)
    {
        unsigned c = clz(t);
        EXPECT_EQ(c, b - 1 - i);
        t = shl(t, 1);
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

TEST_P(Uint256ParamTest, mul_against_add)
{
    const int factor = GetParam();
    for (auto a : numbers)
    {
        uint256 s = 0;
        for (int i = 0; i < factor; ++i)
            s = add(s, a);

        uint256 p = mul(a, factor);
        EXPECT_EQ(p, s);
    }
}
INSTANTIATE_TEST_CASE_P(primes, Uint256ParamTest,
    testing::Values(0, 1, 2, 3, 17, 19, 32, 512, 577, 2048, 2069, 3011, 7919, 8192));