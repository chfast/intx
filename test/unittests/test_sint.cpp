// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "test_suite.hpp"
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <limits>
#include <vector>

using namespace intx;

static_assert(std::is_convertible_v<int64_t, int128>);
static_assert(std::is_convertible_v<uint64_t, int128>);
static_assert(std::is_convertible_v<int128, int256>);
static_assert(!std::is_convertible_v<int256, int128>);
static_assert(std::is_constructible_v<int128, int256>);
static_assert(!std::is_convertible_v<uint128, int128>);
static_assert(std::is_constructible_v<int128, uint128>);
static_assert(!std::is_convertible_v<int128, uint128>);
static_assert(std::is_constructible_v<uint128, int128>);
static_assert(!std::is_convertible_v<int128, int64_t>);
static_assert(std::is_constructible_v<int64_t, int128>);
static_assert(!std::is_constructible_v<int128, double>);
static_assert(!std::is_convertible_v<uint256, int128>);
static_assert(std::is_constructible_v<int128, uint256>);
static_assert(std::is_convertible_v<uint128, int256>);
static_assert(!std::is_convertible_v<int256, uint128>);
static_assert(std::is_constructible_v<uint128, int256>);
static_assert(!std::is_convertible_v<int128, uint256>);
static_assert(std::is_constructible_v<uint256, int128>);
#if INTX_HAS_BUILTIN_INT128
static_assert(!std::is_constructible_v<int128, builtin_int128>);
static_assert(!std::is_constructible_v<int256, builtin_uint128>);
#endif

static_assert(std::numeric_limits<int128>::is_signed);
static_assert(std::numeric_limits<int128>::digits == 127);
static_assert(std::numeric_limits<int128>::digits10 == 38);
static_assert(std::numeric_limits<int256>::digits10 == 76);
static_assert(std::numeric_limits<int256>::lowest() == std::numeric_limits<int256>::min());
static_assert(std::numeric_limits<int256>::min() == int256{-1} << 255);
static_assert(std::numeric_limits<int256>::max() == ~(int256{-1} << 255));
static_assert(from_string<int128>("170141183460469231731687303715884105727") ==
              std::numeric_limits<int128>::max());
static_assert(from_string<int128>("0x7fffffffffffffffffffffffffffffff") ==
              std::numeric_limits<int128>::max());

static_assert(int128{-1} == -int128{1});
static_assert(int256{int128{-2}} == int256{-2});
static_assert(int256{~uint128{}} == (int256{1} << 128) - 1);
static_assert(int256{-1} + uint128{1} == 0);
static_assert(static_cast<uint128>(int256{-2}) == ~uint128{1});
static_assert(int128{~uint256{1}} == -2);
static_assert(static_cast<uint256>(int128{-2}) == ~uint256{1});
static_assert((int256{-8} >> 1) == int256{-4});
static_assert((int256{-8} >> 300) == int256{-1});
static_assert(int128{7} / int128{-2} == int128{-3});
static_assert(int128{7} % int128{-2} == int128{1});
static_assert(smul(-1, -1) == int128{1});
static_assert([] {
    int256 x = -7;
    x += 3;
    x -= 1;
    x *= 2;
    x /= 3;
    x %= 2;
    x &= -2;
    x |= 1;
    x ^= 3;
    x <<= 1;
    x >>= 2;
    return x == -2 && x - 1 == -3 && (x & 3) == 2 && (x ^ 1) == -1 && x <= 0 && x >= -2 &&
           (x <=> 0) < 0 && static_cast<bool>(x) && static_cast<int128>(x) == -2;
}());

namespace
{
template <typename T>
class sint_test : public testing::Test
{
};

struct sint_type_name
{
    template <typename T>
    static std::string GetName(int /*unused*/)
    {
        return "int" + std::to_string(T::num_bits);
    }
};

using sint_types = testing::Types<sint<128>, sint<192>, sint<256>, sint<384>, sint<512>>;
TYPED_TEST_SUITE(sint_test, sint_types, sint_type_name);

template <typename S>
using bits_t = intx::uint<S::num_bits>;

/// The two's complement bits of the builtin integer x extended to N bits.
template <unsigned N, typename T>
intx::uint<N> extend_ref(T x)
{
    if constexpr (std::is_signed_v<T>)
    {
        if (x < 0)
            return ~intx::uint<N>{~static_cast<uint64_t>(x)};
    }
    return intx::uint<N>{static_cast<uint64_t>(x)};
}

/// The arithmetic shift right computed from the logical one.
template <unsigned N>
intx::uint<N> sar_ref(const intx::uint<N>& x, uint64_t shift)
{
    return slt(x, intx::uint<N>{}) ? ~(~x >> shift) : x >> shift;
}

/// Values with all words used and with the sign bit both set and clear.
template <typename S>
std::vector<S> sample_values()
{
    using U = bits_t<S>;
    constexpr auto N = S::num_bits;
    U mixed;
    for (size_t i = 0; i < U::num_words; ++i)
        mixed[i] = 0x0123456789abcdef * (2 * i + 1);
    const U bits[] = {U{}, U{1}, U{2}, U{3}, U{7}, U{1} << 63, U{1} << 64, U{1} << (N - 2),
        U{1} << (N - 1), (U{1} << (N - 1)) + 1, mixed, mixed >> 1, mixed << 64};
    std::vector<S> values;
    for (const auto& b : bits)
    {
        values.emplace_back(b);
        values.emplace_back(~b);
    }
    return values;
}
}  // namespace

TYPED_TEST(sint_test, from_builtin_integer)
{
    using S = TypeParam;
    constexpr auto N = S::num_bits;
    const auto check = [](auto x) { EXPECT_EQ(bits_t<S>{S{x}}, extend_ref<N>(x)) << int64_t(x); };
    for (const auto x : {int64_t{0}, int64_t{1}, int64_t{-1}, int64_t{-2},
             std::numeric_limits<int64_t>::min(), std::numeric_limits<int64_t>::max()})
    {
        check(x);
        check(static_cast<int32_t>(x));
        check(static_cast<int16_t>(x));
        check(static_cast<int8_t>(x));
        check(static_cast<char>(x));
        check(static_cast<uint64_t>(x));
        check(static_cast<uint32_t>(x));
        check(static_cast<uint16_t>(x));
        check(static_cast<uint8_t>(x));
        check(x != 0);
    }
}

TYPED_TEST(sint_test, widening_and_narrowing)
{
    using S = TypeParam;
    using W = sint<S::num_bits + 64>;
    for (const auto& x : sample_values<S>())
    {
        const W w = x;
        EXPECT_EQ(bits_t<W>{w},
            slt(bits_t<S>{x}, {}) ? ~bits_t<W>{~bits_t<S>{x}} : bits_t<W>{bits_t<S>{x}});
        EXPECT_EQ(static_cast<S>(w), x);
        EXPECT_EQ(static_cast<int128>(x), int128{static_cast<uint128>(bits_t<S>{x})});
        EXPECT_EQ(static_cast<bits_t<W>>(x), bits_t<W>{w});
        const W z = bits_t<S>{x};
        EXPECT_EQ(bits_t<W>{z}, bits_t<W>{bits_t<S>{x}});
    }
    for (const auto& y : sample_values<W>())
    {
        const auto u = bits_t<W>{y};
        EXPECT_EQ(bits_t<S>{S{u}}, static_cast<bits_t<S>>(u));
        EXPECT_EQ(static_cast<bits_t<S>>(y), static_cast<bits_t<S>>(u));
    }
}

TYPED_TEST(sint_test, to_builtin_integer)
{
    for (const auto& x : sample_values<TypeParam>())
    {
        const auto w = bits_t<TypeParam>{x}[0];
        EXPECT_EQ(static_cast<int64_t>(x), static_cast<int64_t>(w));
        EXPECT_EQ(static_cast<uint32_t>(x), static_cast<uint32_t>(w));
        EXPECT_EQ(static_cast<int8_t>(x), static_cast<int8_t>(w));
        EXPECT_EQ(static_cast<bool>(x), bits_t<TypeParam>{x} != 0);
    }
}

TYPED_TEST(sint_test, arithmetic)
{
    using S = TypeParam;
    const auto MIN = S{bits_t<S>{1} << (S::num_bits - 1)};
    const auto MAX = ~MIN;
    EXPECT_EQ(MAX + 1, MIN);
    EXPECT_EQ(MIN - 1, MAX);
    EXPECT_EQ(-MIN, MIN);
    EXPECT_EQ(-S{-1}, S{1});
    EXPECT_EQ(S{3} * S{-2}, S{-6});
    EXPECT_EQ(MIN * S{-1}, MIN);

    // The results in the low 128 bits match the ones of int128 (checked against __int128).
    for (const auto& a : sample_values<int128>())
    {
        for (const auto& b : sample_values<int128>())
        {
            const S x = a;
            const S y = b;
            EXPECT_EQ(static_cast<int128>(x + y), a + b);
            EXPECT_EQ(static_cast<int128>(x - y), a - b);
            EXPECT_EQ(static_cast<int128>(x * y), a * b);
            EXPECT_EQ(static_cast<int128>(-x), -a);
            if (b != 0 && (a != int128{1} << 127 || b != -1))
            {
                EXPECT_EQ(x / y, S{a / b});
                EXPECT_EQ(x % y, S{a % b});
            }

            S z = x;
            EXPECT_EQ(z += y, x + y);
            EXPECT_EQ(z -= y, x);
            EXPECT_EQ(z *= y, x * y);
            z = x;
            EXPECT_EQ(z /= y, x / y);
            z = x;
            EXPECT_EQ(z %= y, x % y);
        }
    }
}

TYPED_TEST(sint_test, division)
{
    using S = TypeParam;
    const auto MIN = S{bits_t<S>{1} << (S::num_bits - 1)};
    const auto MAX = ~MIN;
    const std::pair<S, S> cases[][2] = {
        // {{x, y}, {quotient, remainder}}
        {{7, 3}, {2, 1}},
        {{-7, 3}, {-2, -1}},
        {{7, -3}, {-2, 1}},
        {{-7, -3}, {2, -1}},
        {{7, 0}, {0, 0}},
        {{-7, 0}, {0, 0}},
        {{MIN, -1}, {MIN, 0}},
        {{MIN, 1}, {MIN, 0}},
        {{MIN, MAX}, {-1, -1}},
        {{MAX, MIN}, {0, MAX}},
        {{MIN, MIN}, {1, 0}},
    };
    for (const auto& [args, expected] : cases)
    {
        EXPECT_EQ(args.first / args.second, expected.first);
        EXPECT_EQ(args.first % args.second, expected.second);
    }
}

TYPED_TEST(sint_test, comparison)
{
    using S = TypeParam;
    const auto MIN = S{bits_t<S>{1} << (S::num_bits - 1)};
    const auto P64 = S{bits_t<S>{1} << 64};
    const S ordered[] = {MIN, MIN + 1, -P64 - 1, -P64, -P64 + 1, -2, -1, 0, 1, 2, P64 - 1, P64,
        P64 + 1, ~(MIN + 1), ~MIN};
    for (size_t i = 0; i < std::size(ordered); ++i)
    {
        for (size_t j = 0; j < std::size(ordered); ++j)
        {
            const auto& x = ordered[i];
            const auto& y = ordered[j];
            EXPECT_EQ(x == y, i == j);
            EXPECT_EQ(x != y, i != j);
            EXPECT_EQ(x < y, i < j);
            EXPECT_EQ(x > y, i > j);
            EXPECT_EQ(x <= y, i <= j);
            EXPECT_EQ(x >= y, i >= j);
            EXPECT_EQ(x <=> y, i <=> j);
        }
    }
}

TYPED_TEST(sint_test, shift)
{
    using S = TypeParam;
    constexpr uint64_t N = S::num_bits;
    const uint64_t shifts[] = {0, 1, 2, 62, 63, 64, 65, 127, 128, 129, N - 65, N - 64, N - 63,
        N - 2, N - 1, N, N + 1, uint64_t{1} << 63, ~uint64_t{0}};
    for (const auto& x : sample_values<S>())
    {
        for (const auto s : shifts)
        {
            const auto expected_shl = bits_t<S>{x} << s;
            const auto expected_shr = sar_ref(bits_t<S>{x}, s);
            EXPECT_EQ(bits_t<S>{x << s}, expected_shl) << s;
            EXPECT_EQ(bits_t<S>{x >> s}, expected_shr) << s;
            auto y = x;
            EXPECT_EQ(bits_t<S>{y <<= s}, expected_shl);
            y = x;
            EXPECT_EQ(bits_t<S>{y >>= s}, expected_shr);
        }
    }
}

namespace
{
template <typename T, typename S>
concept shiftable_by = requires(T x, S s) {
    x << s;
    x >> s;
    x <<= s;
    x >>= s;
};

template <typename T, typename S>
concept shiftable_by_any = requires(T x, S s) { x << s; } || requires(T x, S s) { x >> s; } ||
                           requires(T x, S s) { x <<= s; } || requires(T x, S s) { x >>= s; };

// Whether the shifts by S are constant expressions. A negative S fails an assertion.
template <typename T, auto S>
concept shl_is_constant = requires { typename std::bool_constant<(T{1} << S) != 0>; };
template <typename T, auto S>
concept shr_is_constant = requires { typename std::bool_constant<(T{1} >> S) != 0>; };
template <typename T>
constexpr T shl_assign(T x, auto shift)
{
    return x <<= shift;
}
template <typename T>
constexpr T shr_assign(T x, auto shift)
{
    return x >>= shift;
}
template <typename T, auto S>
concept shl_assign_is_constant =
    requires { typename std::bool_constant<shl_assign(T{1}, S) != 0>; };
template <typename T, auto S>
concept shr_assign_is_constant =
    requires { typename std::bool_constant<shr_assign(T{1}, S) != 0>; };
}  // namespace

TYPED_TEST(sint_test, shift_by_negative)
{
    using S = TypeParam;
    // MSVC needs the shifts evaluated once before the requires-expressions below.
    static_assert((S{1} << 1) == 2 && (S{2} >> 1) == 1);
    static_assert(shl_assign(S{1}, 1) == 2 && shr_assign(S{2}, 1) == 1);
    static_assert(shl_is_constant<S, 1> && shr_is_constant<S, 1>);
    static_assert(shl_assign_is_constant<S, 1> && shr_assign_is_constant<S, 1>);
#ifndef NDEBUG
    static_assert(!shl_is_constant<S, -1> && !shr_is_constant<S, -1>);
    static_assert(!shl_assign_is_constant<S, -1> && !shr_assign_is_constant<S, -1>);
#endif
}

TYPED_TEST(sint_test, shift_amount_types)
{
    using S = TypeParam;
    static_assert(shiftable_by<S, bool> && shiftable_by<S, int>);
    static_assert(!shiftable_by_any<S, double> && !shiftable_by_any<S, S>);
    static_assert(!shiftable_by_any<S, uint128>);
}

TYPED_TEST(sint_test, bitwise)
{
    using S = TypeParam;
    for (const auto& x : sample_values<S>())
    {
        const auto y = S{bits_t<S>{x} * 0x9e3779b97f4a7c15};
        const auto u = bits_t<S>{x};
        const auto v = bits_t<S>{y};
        EXPECT_EQ(bits_t<S>{~x}, ~u);
        EXPECT_EQ(bits_t<S>{x & y}, u & v);
        EXPECT_EQ(bits_t<S>{x | y}, u | v);
        EXPECT_EQ(bits_t<S>{x ^ y}, u ^ v);
        auto z = x;
        EXPECT_EQ(bits_t<S>{z &= y}, u & v);
        z = x;
        EXPECT_EQ(bits_t<S>{z |= y}, u | v);
        z = x;
        EXPECT_EQ(bits_t<S>{z ^= y}, u ^ v);
    }
}

TEST(sint, numeric_limits)
{
    EXPECT_EQ(std::numeric_limits<int256>::min(), int256{-1} << 255);
    EXPECT_EQ(std::numeric_limits<int256>::max(), ~(int256{-1} << 255));
}

TEST(sint, from_string_out_of_range)
{
    EXPECT_THROW_MESSAGE(from_string<int128>("170141183460469231731687303715884105728"),
        std::out_of_range, "170141183460469231731687303715884105728");
    EXPECT_THROW_MESSAGE(from_string<int128>("0x80000000000000000000000000000000"),
        std::out_of_range, "0x80000000000000000000000000000000");
}

#if INTX_HAS_BUILTIN_INT128
TEST(sint, builtin_int128)
{
    const auto bits = [](const int128& x) {
        return static_cast<builtin_uint128>(static_cast<uint128>(x));
    };
    const auto builtin = [&bits](const int128& x) { return static_cast<builtin_int128>(bits(x)); };
    const auto MIN = static_cast<builtin_int128>(builtin_uint128{1} << 127);
    const auto values = sample_values<int128>();
    for (const auto& x : values)
    {
        const auto a = builtin(x);
        const auto ua = bits(x);
        EXPECT_EQ(bits(-x), -ua);
        for (const auto& y : values)
        {
            const auto b = builtin(y);
            const auto ub = bits(y);
            EXPECT_EQ(bits(x + y), ua + ub);
            EXPECT_EQ(bits(x - y), ua - ub);
            EXPECT_EQ(bits(x * y), ua * ub);
            if (b != 0 && (a != MIN || b != -1))
            {
                EXPECT_EQ(builtin(x / y), a / b);
                EXPECT_EQ(builtin(x % y), a % b);
            }
            EXPECT_EQ(x < y, a < b);
            EXPECT_EQ(x == y, a == b);
        }
        for (int s = 0; s < 128; ++s)
        {
            EXPECT_EQ(builtin(x >> s), a >> s) << s;
            EXPECT_EQ(bits(x << s), ua << s) << s;
        }
    }
}
#endif

TEST(sint, smul)
{
    constexpr auto MIN = std::numeric_limits<int64_t>::min();
    constexpr auto MAX = std::numeric_limits<int64_t>::max();
    static_assert(smul(-1, 1) == -1);
    static_assert(smul(MIN, MIN) == int128{1} << 126);
    static_assert(smul(MAX, MIN) == int128{uint128{0x8000000000000000, 0xc000000000000000}});

    constexpr int64_t inputs[] = {0, 1, 2, 12243, 682017770, 7043980147839196358, MAX, MIN,
        -7043980147839196358, -682017770, -2, -1};
    for (const auto x : inputs)
    {
        for (const auto y : inputs)
            EXPECT_EQ(smul(x, y), int128{x} * int128{y}) << x << " x " << y;
    }
}
