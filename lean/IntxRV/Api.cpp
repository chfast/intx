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

// The functions of the C library that the code calls: their code in the images, proved by hand.
namespace intx::lib
{
[[gnu::used]] constexpr auto* memset = &::memset;
}  // namespace intx::lib

namespace intx::api
{
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
}  // namespace intx::api

// The instances whose RV64 machine code is not proved yet: their specifications are generated
// and their code is in the image (IntxRV/Gen/Code.lean), without the checks. None at present.
namespace intx::wip
{
}  // namespace intx::wip
