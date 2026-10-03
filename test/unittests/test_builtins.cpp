// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace intx;

static constexpr auto is_le = std::endian::native == std::endian::little;
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

TEST(builtins, bit_width_uint64)
{
    EXPECT_EQ(bit_width(uint64_t{0}), 0u);
    EXPECT_EQ(bit_width(uint64_t{1}), 1u);
    EXPECT_EQ(bit_width(uint64_t{2}), 2u);
    EXPECT_EQ(bit_width(uint64_t{0x8000000000000000}), 64u);
}

TEST(builtins, fshl)
{
    static_assert(fshl(0x0123456789abcdef, 0xfedcba9876543210, 0) == 0x0123456789abcdef);
    EXPECT_EQ(fshl(0x0123456789abcdef, 0xfedcba9876543210, 0), 0x0123456789abcdef);
    EXPECT_EQ(fshl(0x0123456789abcdef, 0xfedcba9876543210, 1), 0x02468acf13579bdf);
    EXPECT_EQ(fshl(0x0123456789abcdef, 0xfedcba9876543210, 4), 0x123456789abcdeff);
    EXPECT_EQ(fshl(0x0123456789abcdef, 0xfedcba9876543210, 63), 0xff6e5d4c3b2a1908);
    EXPECT_EQ(fshl(0, 0x8000000000000000, 1), 1);
    EXPECT_EQ(fshl(1, 0, 63), 0x8000000000000000);
}

TEST(builtins, fshr)
{
    static_assert(fshr(0x0123456789abcdef, 0xfedcba9876543210, 0) == 0xfedcba9876543210);
    EXPECT_EQ(fshr(0x0123456789abcdef, 0xfedcba9876543210, 0), 0xfedcba9876543210);
    EXPECT_EQ(fshr(0x0123456789abcdef, 0xfedcba9876543210, 1), 0xff6e5d4c3b2a1908);
    EXPECT_EQ(fshr(0x0123456789abcdef, 0xfedcba9876543210, 4), 0xffedcba987654321);
    EXPECT_EQ(fshr(0x0123456789abcdef, 0xfedcba9876543210, 63), 0x02468acf13579bdf);
    EXPECT_EQ(fshr(1, 0, 1), 0x8000000000000000);
    EXPECT_EQ(fshr(0, 0x8000000000000000, 63), 1);
}

TEST(builtins, shl)
{
    const uint256 x{0x0123456789abcdef, 0xfedcba9876543210, 0x8000000000000001, 0xf000000000000003};
    for (unsigned s = 0; s < 64; ++s)
    {
        uint256 r;
        shl(as_words(r), as_words(x), s);
        EXPECT_EQ(r, x << s) << s;

        intx::uint<320> r1;
        shl(as_words(r1), as_words(x), s);
        EXPECT_EQ(r1, intx::uint<320>{x} << s) << s;

        auto ri = x;  // In place.
        shl(as_words(ri), as_words(std::as_const(ri)), s);
        EXPECT_EQ(ri, x << s) << s;

        // Dynamic sizes.
        intx::uint<320> rd;
        const std::span<const uint64_t> xd{as_words(x)};
        shl(std::span<uint64_t>{as_words(rd)}, xd, s);
        EXPECT_EQ(rd, intx::uint<320>{x} << s) << s;
        rd = 0;
        shl(std::span<uint64_t>{as_words(rd)}.first(4), xd, s);
        EXPECT_EQ(rd, intx::uint<320>{x << s}) << s;
    }

    static_assert([] {
        intx::uint<320> r;
        shl(as_words(r), as_words(uint256{3} << 254), 63);
        return r == intx::uint<320>{3} << 317;
    }());
}

TEST(builtins, shr)
{
    const uint256 x{0x0123456789abcdef, 0xfedcba9876543210, 0x8000000000000001, 0xf000000000000003};
    for (unsigned s = 0; s < 64; ++s)
    {
        uint256 r;
        shr(as_words(r), as_words(x), s);
        EXPECT_EQ(r, x >> s) << s;

        auto ri = x;  // In place.
        shr(as_words(ri), as_words(std::as_const(ri)), s);
        EXPECT_EQ(ri, x >> s) << s;
    }

    static_assert([] {
        uint256 r;
        shr(as_words(r), as_words(uint256{3} << 254), 63);
        return r == uint256{3} << 191;
    }());
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
