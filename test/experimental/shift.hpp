// intx: extended precision integer library.
// Copyright 2021 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

namespace intx
{
namespace experimental
{
[[gnu::noinline]] static uint256 shl(const uint256& x, uint64_t y) noexcept
{
    static auto shift_words = [](uint64_t* r, const uint64_t* u, uint64_t n, uint64_t cnt) {
      u += n;
      r += n;

      const auto tnc = 64 - cnt;
      auto low_limb = *--u;
      auto high_limb = (low_limb << cnt);

      for (uint64_t i = n - 1; i != 0; i--)
      {
          low_limb = *--u;
          *--r = high_limb | (low_limb >> tnc);
          high_limb = (low_limb << cnt);
      }

      *--r = high_limb;
    };

    const auto* xw = as_words(x);

    const auto word_index = y / 64;
    const auto shift = y % 64;

    uint256 rr;
    auto* r = as_words(rr);

    switch (word_index)
    {
    case 0:
        if (shift == 0)
            return x;
        shift_words(r, xw, 4, shift);
        break;

    case 1:
        if (shift == 0)
        {
            r[1] = xw[0];
            r[2] = xw[1];
            r[3] = xw[2];
            return rr;
        }
        shift_words(r + 1, xw, 3, shift);
        return rr;

    case 2:
        if (shift == 0)
        {
            r[2] = xw[0];
            r[3] = xw[1];
            return rr;
        }
        shift_words(r + 2, xw, 2, shift);
        return rr;

    case 3:
        if (shift == 0)
        {
            r[3] = xw[0];
            return rr;
        }
        shift_words(r + 3, xw, 1, shift);
        return rr;

    default:
        break;
    }
    return rr;
}
}  // namespace experimental
}  // namespace intx
