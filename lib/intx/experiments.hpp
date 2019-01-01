// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <cstdint>

namespace intx
{
namespace experiments
{
uint64_t reciprocal(uint64_t d) noexcept;
uint64_t udiv_by_reciprocal(uint64_t u, uint64_t d) noexcept;
}  // namespace experiments
}  // namespace intx
