// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "random.hpp"
#include <intx/intx.hpp>

namespace intx::test
{
namespace
{
std::array<uint64_t, num_samples> samples_64_norm;
std::array<uint128, num_samples> samples_128_norm;
std::array<uint256, num_samples> samples_256[lt_x_256 - x_64 + 1];
std::array<uint512, num_samples> samples_512[y_512 - x_64 + 1];
std::array<uint64_t, num_samples> samples_shift_w[4];
std::array<uint64_t, num_samples> samples_shift_mixed;

uint64_t* as_words(uint64_t& x) noexcept
{
    return &x;
}

bool init() noexcept
{
    std::mt19937_64 rng{0};  // NOLINT(cert-msc51-cpp,cert-msc32-c)

    const auto gen_int = [&rng](auto& out, int num_significant_words) noexcept {
        std::generate_n(as_words(out), num_significant_words,
            [&rng] { return std::uniform_int_distribution<uint64_t>{}(rng); });
    };

    const auto lt_fixup = [&rng](uint256& tgt, const uint256& src) noexcept {
        if (tgt[3] > src[3])
            tgt[3] = std::uniform_int_distribution<uint64_t>{0, src[3]}(rng);
        assert(tgt <= src);
    };

    for (size_t i = 0; i < num_samples; ++i)
    {
        gen_int(samples_64_norm[i], 1);
        samples_64_norm[i] |= 0x8000000000000000;

        gen_int(samples_128_norm[i], 2);
        samples_128_norm[i][1] |= 0x8000000000000000;

        gen_int(samples_256[x_64][i], 1);
        gen_int(samples_256[y_64][i], 1);
        samples_512[x_64][i] = samples_256[x_64][i];

        gen_int(samples_256[x_128][i], 2);
        gen_int(samples_256[y_128][i], 2);
        samples_512[x_128][i] = samples_256[x_128][i];

        gen_int(samples_256[x_192][i], 3);
        gen_int(samples_256[y_192][i], 3);
        samples_512[x_192][i] = samples_256[x_192][i];

        gen_int(samples_256[x_256][i], 4);
        gen_int(samples_256[y_256][i], 4);
        gen_int(samples_256[lt_256][i], 4);
        gen_int(samples_256[lt_x_256][i], 4);

        lt_fixup(samples_256[lt_256][i], samples_256[x_256][i]);
        lt_fixup(samples_256[lt_256][i], samples_256[y_256][i]);
        lt_fixup(samples_256[lt_x_256][i], samples_256[x_256][i]);

        samples_512[x_256][i] = samples_256[x_256][i];
        samples_512[y_256][i] = samples_256[y_256][i];
        samples_512[lt_256][i] = samples_256[lt_256][i];
        samples_512[lt_x_256][i] = samples_256[lt_x_256][i];

        gen_int(samples_512[x_512][i], 8);
        gen_int(samples_512[y_512][i], 8);
    }

    // Generate samples for shift amounts: ranges, 0-64, 0-128, ... and mix of those.
    for (size_t w = 0; w < 4; ++w)
    {
        std::ranges::generate(samples_shift_w[w], [&rng, w]() noexcept {
            return std::uniform_int_distribution<uint64_t>{w * 64, (w + 1) * 64 - 1}(rng);
        });
        std::copy_n(std::begin(samples_shift_w[w]), num_samples / 4,
            &samples_shift_mixed[(num_samples / 4) * w]);

        std::copy_n(std::begin(samples_256[x_64 + w]), num_samples / 4,
            &samples_256[x_256_mixed][(num_samples / 4) * w]);
        std::copy_n(std::begin(samples_256[y_64 + w]), num_samples / 4,
            &samples_256[y_256_mixed][(num_samples / 4) * w]);
    }
    std::ranges::shuffle(samples_shift_mixed, rng);

    auto rng_copy = rng;
    std::ranges::shuffle(samples_256[x_256_mixed], rng);
    std::ranges::shuffle(samples_256[y_256_mixed], rng_copy);

    return true;
}

const auto _ = init();
}  // namespace

template <>
const std::array<uint64_t, num_samples>& get_samples<uint64_t>(samples_set_id id) noexcept
{
    switch (id)
    {
    case norm:
        return samples_64_norm;
    case shift_w0:
    case shift_w1:
    case shift_w2:
    case shift_w3:
        return samples_shift_w[id - shift_w0];
    case shift_mixed:
        return samples_shift_mixed;
    default:
        std::abort();
    }
}

template <>
const std::array<uint128, num_samples>& get_samples<uint128>(samples_set_id id) noexcept
{
    if (id != norm)
        std::abort();
    return samples_128_norm;
}

template <>
const std::array<uint256, num_samples>& get_samples<uint256>(samples_set_id id) noexcept
{
    return samples_256[id];
}

template <>
const std::array<uint512, num_samples>& get_samples<uint512>(samples_set_id id) noexcept
{
    return samples_512[id];
}

}  // namespace intx::test
