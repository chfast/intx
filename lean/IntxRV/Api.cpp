// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

// The instances of the functions of intx that are verified against the specifications in their
// documentation in intx.hpp (the @pre and @post commands).
//
// Each instance is a lambda that calls one documented function (the operators are hidden friends,
// so they have no qualified name to point to) or the address of a function template instance, the
// out-of-line function that other functions call. A lambda with [[gnu::flatten]] gets the code of a
// function that clang does not inline otherwise. scripts/rv_api.py finds the function in the AST
// of this file and states its specification for the instance:
// - intx::api: a [[gnu::used]] pointer `p` whose RV64 machine code is proved (the specification
//   `Api.p.spec` in the generated IntxRV/Gen/Api.lean, the proof in IntxRV/Api/p.lean),
// - intx::model: a function whose model in Lean is proved (the generated Intx/Gen/Spec.lean, the
//   model Intx.Model.<name>, the proofs in Intx/Proofs/); none at present.

#include <intx/intx.hpp>

// The attributes of lambdas before the parameters, of C++23, are an extension of clang in C++20.
#pragma clang diagnostic ignored "-Wc++23-lambda-attributes"

// memset() for the calls that clang emits to zero more than 64 bytes, as the results of udivrem()
// for addmod() and mulmod(): one byte at a time, so that clang does not make it a call of itself.
// Its proof is in IntxRV/Memset.lean.
extern "C" [[clang::no_builtin("memset")]] void* memset(void* dst, int c, size_t n) noexcept
{
    auto* const p = static_cast<unsigned char*>(dst);
    for (size_t i = 0; i != n; ++i)
        p[i] = static_cast<unsigned char>(c);
    return dst;
}

// memcpy() for the calls that clang emits to copy the bytes of a buffer of any alignment, as in
// be::load(): one byte at a time. Its proof is in IntxRV/Memcpy.lean.
extern "C" [[clang::no_builtin("memcpy")]] void* memcpy(
    void* dst, const void* src, size_t n) noexcept
{
    auto* const d = static_cast<unsigned char*>(dst);
    const auto* const s = static_cast<const unsigned char*>(src);
    for (size_t i = 0; i != n; ++i)
        d[i] = s[i];
    return dst;
}

// The functions of the C library that the code calls: their code in the images, proved by hand.
namespace intx::lib
{
[[gnu::used]] constexpr auto* memset = &::memset;
[[gnu::used]] constexpr auto* memcpy = &::memcpy;
}  // namespace intx::lib

// The layouts of evmc::bytes32 and evmc::address, which the interpreter of evmone converts to and
// from uint256 with be::.
namespace intx::evm
{
struct Bytes32
{
    uint8_t bytes[32];
};
struct Address
{
    uint8_t bytes[20];
};
}  // namespace intx::evm

namespace intx::api
{
using namespace evm;
using Binop = uint256 (*)(const uint256&, const uint256&) noexcept;
using Cmp = bool (*)(const uint256&, const uint256&) noexcept;

[[gnu::used]] constexpr auto* umul =
    +[](uint64_t x, uint64_t y) noexcept { return intx::umul(x, y); };
[[gnu::used]] constexpr auto* addc =
    +[](uint64_t x, uint64_t y, bool carry) noexcept { return intx::addc(x, y, carry); };
[[gnu::used]] constexpr auto* reciprocal_2by1 =
    +[](uint64_t d) noexcept { return intx::reciprocal_2by1(d); };
[[gnu::used]] constexpr auto* reciprocal_3by2 =
    +[](uint128 d) noexcept { return intx::reciprocal_3by2(d); };
[[gnu::used]] constexpr auto* udivrem_2by1 =
    +[](uint128 u, uint64_t d, uint64_t v) noexcept { return intx::udivrem_2by1(u, d, v); };
[[gnu::used]] constexpr auto* udivrem_3by2 =
    +[](uint64_t u2, uint64_t u1, uint64_t u0, uint128 d, uint64_t v) noexcept {
        return intx::udivrem_3by2(u2, u1, u0, d, v);
    };

[[gnu::used]] constexpr auto* umul_256 = &intx::umul<256>;
[[gnu::used]] constexpr auto* udivrem_by1 = &intx::internal::udivrem_by1<std::dynamic_extent>;
[[gnu::used]] constexpr auto* udivrem_by2 = &intx::internal::udivrem_by2<std::dynamic_extent>;
[[gnu::used]] constexpr auto* udivrem_top1_2 = &intx::internal::udivrem_top1<2, 256, 256>;
[[gnu::used]] constexpr auto* udivrem_top1_3 = &intx::internal::udivrem_top1<3, 256, 256>;
[[gnu::used]] constexpr auto* udivrem_top2_3 = &intx::internal::udivrem_top2<3, false, 256, 256>;
// The division: calls to the divisions by 1 and 2 words and of the top words.
[[gnu::used]] constexpr auto* udivrem_256 = &intx::udivrem<256, 256>;
[[gnu::used]] constexpr auto* shl_9_8 = &intx::shl<9, 8>;
[[gnu::used]] constexpr Binop add_256 = [](const uint256& x, const uint256& y) noexcept {
    return x + y;
};
[[gnu::used]] constexpr Binop sub_256 = [](const uint256& x, const uint256& y) noexcept {
    return x - y;
};
[[gnu::used]] constexpr Binop mul_256 = [](const uint256& x, const uint256& y) noexcept {
    return x * y;
};
[[gnu::used]] constexpr Cmp eq_256 = [](const uint256& x, const uint256& y) noexcept {
    return x == y;
};
[[gnu::used]] constexpr Cmp ne_256 = [](const uint256& x, const uint256& y) noexcept {
    return x != y;
};
[[gnu::used]] constexpr Cmp lt_256 = [](const uint256& x, const uint256& y) noexcept {
    return x < y;
};
[[gnu::used]] constexpr Cmp gt_256 = [](const uint256& x, const uint256& y) noexcept {
    return x > y;
};
[[gnu::used]] constexpr Cmp ge_256 = [](const uint256& x, const uint256& y) noexcept {
    return x >= y;
};
[[gnu::used]] constexpr Cmp le_256 = [](const uint256& x, const uint256& y) noexcept {
    return x <= y;
};
[[gnu::used]] constexpr Cmp slt_256 = [](const uint256& x, const uint256& y) noexcept {
    return slt(x, y);
};
[[gnu::used]] constexpr Binop or_256 = [](const uint256& x, const uint256& y) noexcept {
    return x | y;
};
[[gnu::used]] constexpr Binop and_256 = [](const uint256& x, const uint256& y) noexcept {
    return x & y;
};
[[gnu::used]] constexpr Binop xor_256 = [](const uint256& x, const uint256& y) noexcept {
    return x ^ y;
};
[[gnu::used]] constexpr auto* not_256 = +[](const uint256& x) noexcept { return ~x; };
[[gnu::used]] constexpr auto* bit_test_256 =
    +[](const uint256& x, size_t i) noexcept { return bit_test(x, i); };
[[gnu::used]] constexpr auto* count_significant_words_256 =
    +[](const uint256& x) noexcept { return count_significant_words(x); };
[[gnu::used]] constexpr auto* clz_256 = +[](const uint256& x) noexcept { return clz(x); };
[[gnu::used]] constexpr auto* bit_width_256 =
    +[](const uint256& x) noexcept { return bit_width(x); };
[[gnu::used]] constexpr auto* ctz_256 = +[](const uint256& x) noexcept { return ctz(x); };
[[gnu::used]] constexpr auto* shl_256 =
    +[] [[gnu::flatten]] (const uint256& x, uint64_t shift) noexcept { return x << shift; };
[[gnu::used]] constexpr auto* shr_256 =
    +[] [[gnu::flatten]] (const uint256& x, uint64_t shift) noexcept { return x >> shift; };
[[gnu::used]] constexpr Binop shl_256_by_256 =
    [] [[gnu::flatten]] (const uint256& x, const uint256& shift) noexcept { return x << shift; };
[[gnu::used]] constexpr Binop shr_256_by_256 =
    [] [[gnu::flatten]] (const uint256& x, const uint256& shift) noexcept { return x >> shift; };
// The division and the remainder: a call of udivrem<256, 256>().
[[gnu::used]] constexpr Binop div_256 = [](const uint256& x, const uint256& y) noexcept {
    return x / y;
};
[[gnu::used]] constexpr Binop mod_256 = [](const uint256& x, const uint256& y) noexcept {
    return x % y;
};
// The overload of submul() in place, which the Knuth division calls.
using Submul = uint64_t (*)(uint64_t[], std::span<const uint64_t>, uint64_t) noexcept;
[[gnu::used]] constexpr Submul submul = &intx::internal::submul;
// The Knuth divisions by 3 and 4 words of udivrem<512, 256>(), which call submul().
[[gnu::used]] constexpr auto* udivrem_knuth_normalized_3 =
    &intx::internal::udivrem_knuth_normalized<3>;
[[gnu::used]] constexpr auto* udivrem_knuth_normalized_4 =
    &intx::internal::udivrem_knuth_normalized<4>;
// The division of the 512-bit product in mulmod().
[[gnu::used]] constexpr auto* udivrem_512_256 = &intx::udivrem<512, 256>;
[[gnu::used]] constexpr auto* mulmod_256 = &intx::mulmod;
// The division in addmod() and its callees.
[[gnu::used]] constexpr auto* udivrem_320_256 = &intx::udivrem<320, 256>;
[[gnu::used]] constexpr auto* udivrem_by1_5 = &intx::internal::udivrem_by1<5>;
[[gnu::used]] constexpr auto* udivrem_by2_4 = &intx::internal::udivrem_by2<4>;
[[gnu::used]] constexpr auto* udivrem_top1_2_320 = &intx::internal::udivrem_top1<2, 320, 256>;
[[gnu::used]] constexpr auto* udivrem_top1_3_320 = &intx::internal::udivrem_top1<3, 320, 256>;
[[gnu::used]] constexpr auto* udivrem_top2_3_320 =
    &intx::internal::udivrem_top2<3, false, 320, 256>;
[[gnu::used]] constexpr auto* udivrem_knuth_normalized =
    &intx::internal::udivrem_knuth_normalized<std::dynamic_extent>;
[[gnu::used]] constexpr auto* udivrem_knuth_320 =
    &intx::internal::udivrem_knuth<320, 256, std::dynamic_extent>;
[[gnu::used]] constexpr auto* udivrem_top2_3_equal_320 =
    &intx::internal::udivrem_top2<3, true, 320, 256>;
[[gnu::used]] constexpr auto* udivrem_top2_4_320 =
    &intx::internal::udivrem_top2<4, false, 320, 256>;
// addmod(), which divides the 320-bit sum with udivrem<320, 256>().
[[gnu::used]] constexpr auto* addmod_256 = &intx::addmod;
// The negation.
[[gnu::used]] constexpr auto* neg_256 = +[](const uint256& x) noexcept { return -x; };
// sdivrem(), which calls udivrem<256, 256>().
[[gnu::used]] constexpr auto* sdivrem_256 = &intx::sdivrem<256>;
[[gnu::used]] constexpr auto* count_significant_bytes_256 = &intx::count_significant_bytes<256>;
// exp(), which calls operator<< by uint64_t.
[[gnu::used]] constexpr auto* exp_256 = &intx::exp<256>;
// The uses of the interpreter of evmone: the conversions to and from builtin integers.
[[gnu::used]] constexpr auto* bool_256 =
    +[](const uint256& x) noexcept { return static_cast<bool>(x); };
[[gnu::used]] constexpr auto* to_u64_256 =
    +[](const uint256& x) noexcept { return static_cast<uint64_t>(x); };
[[gnu::used]] constexpr auto* to_i64_256 =
    +[](const uint256& x) noexcept { return static_cast<int64_t>(x); };
[[gnu::used]] constexpr auto* to_u8_256 =
    +[](const uint256& x) noexcept { return static_cast<uint8_t>(x); };
[[gnu::used]] constexpr auto* to_i32_256 =
    +[](const uint256& x) noexcept { return static_cast<int>(x); };
[[gnu::used]] constexpr auto* from_i32_256 = +[](int v) noexcept { return uint256{v}; };
[[gnu::used]] constexpr auto* assign_256 = +[](uint256& x, uint64_t v) noexcept { x = v; };
// The operators in place.
[[gnu::used]] constexpr auto* add_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x += y; };
[[gnu::used]] constexpr auto* and_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x &= y; };
[[gnu::used]] constexpr auto* or_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x |= y; };
[[gnu::used]] constexpr auto* xor_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x ^= y; };
[[gnu::used]] constexpr auto* mul_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x *= y; };
[[gnu::used]] constexpr auto* shl_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x <<= y; };
[[gnu::used]] constexpr auto* shr_assign_256 =
    +[](uint256& x, const uint256& y) noexcept { x >>= y; };
// The comparisons with builtin integers.
[[gnu::used]] constexpr auto* lt_256_i32 = +[](const uint256& x, int y) noexcept { return x < y; };
[[gnu::used]] constexpr auto* lt_256_i64 =
    +[](const uint256& x, int64_t y) noexcept { return x < y; };
[[gnu::used]] constexpr auto* lt_256_u64 =
    +[](const uint256& x, uint64_t y) noexcept { return x < y; };
[[gnu::used]] constexpr auto* lt_u64_256 =
    +[](uint64_t x, const uint256& y) noexcept { return x < y; };
[[gnu::used]] constexpr auto* lt_u32_256 =
    +[](uint32_t x, const uint256& y) noexcept { return x < y; };
[[gnu::used]] constexpr auto* lt_i32_256 = +[](int x, const uint256& y) noexcept { return x < y; };
// The conversions to and from bytes of big-endian order.
[[gnu::used]] constexpr auto* be_load_u64 =
    +[](const uint8_t* p) noexcept { return be::unsafe::load<uint64_t>(p); };
[[gnu::used]] constexpr auto* be_load_u16 =
    +[](const uint8_t* p) noexcept { return be::unsafe::load<uint16_t>(p); };
[[gnu::used]] constexpr auto* be_load_u32 =
    +[](const uint8_t* p) noexcept { return be::unsafe::load<uint32_t>(p); };
[[gnu::used]] constexpr auto* be_store_u64 =
    +[](uint8_t* p, uint64_t x) noexcept { be::unsafe::store(p, x); };
[[gnu::used]] constexpr auto* be_load_256 =
    +[](const uint8_t* p) noexcept { return be::unsafe::load<uint256>(p); };
[[gnu::used]] constexpr auto* be_load_256_32 =
    +[](const uint8_t (&p)[32]) noexcept { return be::load<uint256>(p); };
[[gnu::used]] constexpr auto* be_load_256_bytes32 =
    +[](const Bytes32& p) noexcept { return be::load<uint256>(p); };
[[gnu::used]] constexpr auto* be_load_256_address =
    +[](const Address& p) noexcept { return be::load<uint256>(p); };
[[gnu::used]] constexpr auto* be_store_256 =
    +[](uint8_t* p, const uint256& x) noexcept { be::unsafe::store(p, x); };
[[gnu::used]] constexpr auto* be_store_bytes32 =
    +[](const uint256& x) noexcept { return be::store<Bytes32>(x); };
[[gnu::used]] constexpr auto* be_trunc_address =
    +[](const uint256& x) noexcept { return be::trunc<Address>(x); };
}  // namespace intx::api

// The instances whose RV64 machine code is not proved yet: their specifications are generated
// and their code is in the image (IntxRV/Gen/Code.lean), without the checks.
namespace intx::wip
{
}  // namespace intx::wip
