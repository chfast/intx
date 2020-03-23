// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>

namespace intx
{
namespace experimental
{
div_result<uint128> udivrem_4by2(const uint256& u, uint128 d) noexcept;
div_result<uint128, uint256> udivrem_6by4(const uint64_t* u, const uint256& d) noexcept;
}  // namespace experimental
}  // namespace intx
