// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <gtest/gtest.h>
#include <intx/intx.hpp>

#pragma warning(disable : 4307)

using namespace intx;

static_assert(clz_generic(uint32_t{0}) == 32);
static_assert(clz_generic(uint32_t{1}) == 31);
static_assert(clz_generic(uint32_t{3}) == 30);
static_assert(clz_generic(uint32_t{9}) == 28);

static_assert(clz_generic(uint64_t{0}) == 64);
static_assert(clz_generic(uint64_t{1}) == 63);
static_assert(clz_generic(uint64_t{3}) == 62);
static_assert(clz_generic(uint64_t{9}) == 60);

static constexpr auto is_le = byte_order_is_little_endian;
static_assert(to_little_endian(uint8_t{0x0a}) == 0x0a);
static_assert(to_little_endian(uint16_t{0x0b0a}) == (is_le ? 0x0b0a : 0x0a0b));
static_assert(to_little_endian(uint32_t{0x0d0c0b0a}) == (is_le ? 0x0d0c0b0a : 0x0a0b0c0d));
static_assert(to_little_endian(uint64_t{0x02010f0e0d0c0b0a}) ==
              (is_le ? 0x02010f0e0d0c0b0a : 0x0a0b0c0d0e0f0102));
static_assert(to_big_endian(uint8_t{0x0a}) == 0x0a);
static_assert(to_big_endian(uint16_t{0x0b0a}) == (is_le ? 0x0a0b : 0x0b0a));
static_assert(to_big_endian(uint32_t{0x0d0c0b0a}) == (is_le ? 0x0a0b0c0d : 0x0d0c0b0a));
static_assert(to_big_endian(uint64_t{0x02010f0e0d0c0b0a}) ==
              (is_le ? 0x0a0b0c0d0e0f0102 : 0x02010f0e0d0c0b0a));

static_assert(addc(0, 0).value == 0);
static_assert(!addc(0, 0).carry);
static_assert(addc(0xffffffffffffffff, 2).value == 1);
static_assert(addc(0xffffffffffffffff, 2).carry);

static_assert(subc(0, 0).value == 0);
static_assert(!subc(0, 0).carry);
static_assert(subc(0, 1).value == 0xffffffffffffffff);
static_assert(subc(0, 1).carry);


TEST(builtins, clz64_single_one)
{
    for (unsigned i = 0; i <= 63; ++i)
    {
        const auto input = (uint64_t{1} << 63) >> i;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz64_two_ones)
{
    for (unsigned i = 0; i <= 63; ++i)
    {
        const auto input = ((uint64_t{1} << 63) >> i) | 1;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz32_single_one)
{
    for (unsigned i = 0; i <= 31; ++i)
    {
        const auto input = (uint32_t{1} << 31) >> i;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz32_two_ones)
{
    for (unsigned i = 0; i <= 31; ++i)
    {
        const auto input = ((uint32_t{1} << 31) >> i) | 1;
        EXPECT_EQ(clz(input), i);
        EXPECT_EQ(clz_generic(input), i);
    }
}

TEST(builtins, clz_zero)
{
    EXPECT_EQ(clz(uint32_t{0}), 32u);
    EXPECT_EQ(clz_generic(uint32_t{0}), 32u);
    EXPECT_EQ(clz(uint64_t{0}), 64u);
    EXPECT_EQ(clz_generic(uint64_t{0}), 64u);
}

TEST(builtins, count_significant_bytes)
{
    static_assert(count_significant_bytes(0) == 0);

    static_assert(count_significant_bytes(1) == 1);
    static_assert(count_significant_bytes(0x80) == 1);
    static_assert(count_significant_bytes(0xff) == 1);

    static_assert(count_significant_bytes(0x100) == 2);
    static_assert(count_significant_bytes(0x8000) == 2);
    static_assert(count_significant_bytes(0xffff) == 2);

    static_assert(count_significant_bytes(0x10000) == 3);
    static_assert(count_significant_bytes(0x800000) == 3);
    static_assert(count_significant_bytes(0xffffff) == 3);

    static_assert(count_significant_bytes(0x1000000) == 4);
    static_assert(count_significant_bytes(0x80000000) == 4);
    static_assert(count_significant_bytes(0xffffffff) == 4);

    static_assert(count_significant_bytes(0x100000000) == 5);
    static_assert(count_significant_bytes(0x8000000000) == 5);
    static_assert(count_significant_bytes(0xffffffffff) == 5);

    static_assert(count_significant_bytes(0x10000000000) == 6);
    static_assert(count_significant_bytes(0x800000000000) == 6);
    static_assert(count_significant_bytes(0xffffffffffff) == 6);

    static_assert(count_significant_bytes(0x1000000000000) == 7);
    static_assert(count_significant_bytes(0x80000000000000) == 7);
    static_assert(count_significant_bytes(0xffffffffffffff) == 7);

    static_assert(count_significant_bytes(0x100000000000000) == 8);
    static_assert(count_significant_bytes(0x8000000000000000) == 8);
    static_assert(count_significant_bytes(0xffffffffffffffff) == 8);

    uint64_t x = 0;
    EXPECT_EQ(count_significant_bytes(x), 0u);
    x = 1;
    EXPECT_EQ(count_significant_bytes(x), 1u);
    x = 0x80;
    EXPECT_EQ(count_significant_bytes(x), 1u);
    x = 0x100000000000000;
    EXPECT_EQ(count_significant_bytes(x), 8u);
    x = 0x8000000000000000;
    EXPECT_EQ(count_significant_bytes(x), 8u);
}

namespace
{
constexpr int func() noexcept
{
    return is_constant_evaluated() ? 1 : 2;
}
}  // namespace

TEST(builtins, is_constant_evaluated)
{
    constexpr auto is_constexpr_true = is_constant_evaluated();
    EXPECT_TRUE(is_constexpr_true);
    constexpr auto constexpr_func_res = func();
    EXPECT_EQ(constexpr_func_res, 1);

    auto is_constexpr_false = is_constant_evaluated();
    auto nonconstexpr_func_res = func();

#if (defined(__clang__) && __clang_major__ >= 9) || (defined(__GNUC__) && __GNUC__ >= 10) || \
    (defined(_MSC_VER) && _MSC_VER >= 1925)
    EXPECT_FALSE(is_constexpr_false);
    EXPECT_EQ(nonconstexpr_func_res, 2);
#else
    EXPECT_TRUE(is_constexpr_false);
    EXPECT_EQ(nonconstexpr_func_res, 1);
#endif
}

static_assert(bswap(uint8_t{0x81}) == 0x81);
static_assert(bswap(uint16_t{0x8681}) == 0x8186);
static_assert(bswap(uint32_t{0x86818082}) == 0x82808186);
static_assert(bswap(uint64_t{0x8680808081808082}) == 0x8280808180808086);
TEST(builtins, bswap)
{
    uint8_t x8 = 0x86;
    EXPECT_EQ(bswap(x8), 0x86);
    uint16_t x16 = 0x8681;
    EXPECT_EQ(bswap(x16), 0x8186);
    uint32_t x32 = 0x86818082;
    EXPECT_EQ(bswap(x32), 0x82808186);
    uint64_t x64 = 0x8680808081808082;
    EXPECT_EQ(bswap(x64), 0x8280808180808086);
    uint128 x128 = uint128{0x8680808081808082, 0x8080838080848085};
    EXPECT_EQ(bswap(x128), (uint128{0x8580848080838080, 0x8280808180808086}));
}

TEST(builtins, be_load_uint8_t)
{
    constexpr auto size = sizeof(uint8_t);
    uint8_t data[size]{};
    data[0] = 0x81;
    const auto expected = 0x81;
    EXPECT_EQ(be::unsafe::load<uint8_t>(data), expected);
    EXPECT_EQ(be::load<uint8_t>(data), expected);
}

TEST(builtins, be_load_uint16_t)
{
    constexpr auto size = sizeof(uint16_t);
    uint8_t data[size]{};
    data[0] = 0x80;
    data[size - 1] = 1;
    const auto expected = (uint16_t{1} << (sizeof(uint16_t) * 8 - 1)) | 1;
    EXPECT_EQ(be::unsafe::load<uint16_t>(data), expected);
    EXPECT_EQ(be::load<uint16_t>(data), expected);
}

TEST(builtins, be_load_uint32_t)
{
    constexpr auto size = sizeof(uint32_t);
    uint8_t data[size]{};
    data[0] = 0x80;
    data[size - 1] = 1;
    const auto expected = (uint32_t{1} << (sizeof(uint32_t) * 8 - 1)) | 1;
    EXPECT_EQ(be::unsafe::load<uint32_t>(data), expected);
    EXPECT_EQ(be::load<uint32_t>(data), expected);
}

TEST(builtins, be_load_uint64_t)
{
    constexpr auto size = sizeof(uint64_t);
    uint8_t data[size]{};
    data[0] = 0x80;
    data[size - 1] = 1;
    const auto expected = (uint64_t{1} << (sizeof(uint64_t) * 8 - 1)) | 1;
    EXPECT_EQ(be::unsafe::load<uint64_t>(data), expected);
    EXPECT_EQ(be::load<uint64_t>(data), expected);
}

TEST(builtins, be_load_partial)
{
    uint8_t data[1]{0xec};
    EXPECT_EQ(be::load<uint64_t>(data), uint64_t{0xec});
    EXPECT_EQ(be::load<uint32_t>(data), uint32_t{0xec});
    EXPECT_EQ(be::load<uint16_t>(data), uint16_t{0xec});
}

TEST(builtins, be_store_uint64_t)
{
    constexpr auto size = sizeof(uint64_t);
    uint8_t data[size]{};
    std::string_view view{reinterpret_cast<const char*>(data), std::size(data)};
    be::store(data, uint64_t{0x0102030405060708});
    EXPECT_EQ(view, "\x01\x02\x03\x04\x05\x06\x07\x08");
    std::fill_n(data, std::size(data), uint8_t{0});
    be::unsafe::store(data, uint64_t{0x0102030405060708});
    EXPECT_EQ(view, "\x01\x02\x03\x04\x05\x06\x07\x08");
}

TEST(builtins, le_load_uint32_t)
{
    const uint8_t data[] = {0xb1, 0xb2, 0xb3, 0xb4};
    EXPECT_EQ(le::load<uint32_t>(data), 0xb4b3b2b1);
    EXPECT_EQ(le::unsafe::load<uint32_t>(data), 0xb4b3b2b1);
}

TEST(builtins, le_store_uint32_t)
{
    uint8_t data[] = {0xb1, 0xb2, 0xb3, 0xb4};
    std::string_view view{reinterpret_cast<const char*>(data), std::size(data)};
    le::store(data, uint32_t{0xa1a2a3a4});
    EXPECT_EQ(view, "\xa4\xa3\xa2\xa1");
    std::fill_n(data, std::size(data), uint8_t{0xff});
    le::unsafe::store(data, uint32_t{0xc1c2c3c4});
    EXPECT_EQ(view, "\xc4\xc3\xc2\xc1");
}
