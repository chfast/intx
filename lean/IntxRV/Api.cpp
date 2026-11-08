// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

// The instances of the functions of intx that are verified against the specifications in their
// documentation in intx.hpp (the @pre and @post commands).
//
// Each instance is a lambda that calls one documented function: the operators are hidden friends,
// so they have no qualified name to point to. scripts/rv_api.py finds the function that the lambda
// calls in the AST of this file and states its specification for the instance:
// - intx::api: a [[gnu::used]] pointer whose RV64 machine code is proved (IntxRV/Gen/Api.lean,
//   the proofs in IntxRV/Api/),
// - intx::model: a function whose model in Lean is proved (Intx/Gen/Spec.lean, the model
//   Intx.Model.<name>, the proofs in Intx/Proofs/); none at present.

#include <intx/intx.hpp>

namespace intx::api
{
using Binop = uint256 (*)(const uint256&, const uint256&) noexcept;
using Cmp = bool (*)(const uint256&, const uint256&) noexcept;

[[gnu::used]] constexpr auto* umul =
    +[](uint64_t x, uint64_t y) noexcept { return intx::umul(x, y); };
[[gnu::used]] constexpr auto* addc =
    +[](uint64_t x, uint64_t y, bool carry) noexcept { return intx::addc(x, y, carry); };
[[gnu::used]] constexpr auto* udivrem_2by1 =
    +[](uint128 u, uint64_t d, uint64_t v) noexcept { return intx::udivrem_2by1(u, d, v); };

[[gnu::used]] constexpr Binop add_256 = [](const uint256& x, const uint256& y) noexcept {
    return x + y;
};
[[gnu::used]] constexpr Binop sub_256 = [](const uint256& x, const uint256& y) noexcept {
    return x - y;
};
[[gnu::used]] constexpr Cmp eq_256 = [](const uint256& x, const uint256& y) noexcept {
    return x == y;
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
}  // namespace intx::api
