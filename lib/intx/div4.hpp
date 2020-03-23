// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include <intx/intx.hpp>

namespace intx
{
namespace experimental
{
div_result<uint128> udivrem_4by2(uint256 u, uint128 d) noexcept;
}
}  // namespace intx
