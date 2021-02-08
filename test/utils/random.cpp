// intx: extended precision integer library.
// Copyright 2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

#include "random.hpp"
#include <intx/intx.hpp>

namespace intx
{
namespace test
{
namespace
{
std::array<uint64_t, num_samples> samples_64_norm;
std::array<uint128, num_samples> samples_128_norm;
std::array<uint256, num_samples> samples_256[lt_256 - x_64 + 1];
std::array<uint512, num_samples> samples_512[y_512 - x_64 + 1];

uint64_t* as_words(uint64_t& x) noexcept
{
    return &x;
}

bool init() noexcept
{
    std::mt19937_64 rng{0};  // NOLINT(cert-msc51-cpp)

    const auto gen_int = [&rng](auto& out, int num_significant_words) noexcept {
        std::generate_n(as_words(out), num_significant_words,
            [&rng] { return std::uniform_int_distribution<uint64_t>{}(rng); });
    };

    for (size_t i = 0; i < num_samples; ++i)
    {
        gen_int(samples_64_norm[i], 1);
        samples_64_norm[i] |= 0x8000000000000000;

        gen_int(samples_128_norm[i], 2);
        samples_128_norm[i].words[1] |= 0x8000000000000000;

        gen_int(samples_256[x_64][i], 1);
        samples_512[x_64][i] = samples_256[x_64][i];

        gen_int(samples_256[x_128][i], 2);
        samples_512[x_128][i] = samples_256[x_128][i];

        gen_int(samples_256[x_192][i], 3);
        samples_512[x_192][i] = samples_256[x_192][i];

        gen_int(samples_256[x_256][i], 4);
        gen_int(samples_256[y_256][i], 4);
        gen_int(samples_256[lt_256][i], 4);

        if (samples_256[lt_256][i] > samples_256[x_256][i])
            std::swap(samples_256[lt_256][i], samples_256[x_256][i]);

        if (samples_256[lt_256][i] > samples_256[x_256][i])
            std::swap(samples_256[lt_256][i], samples_256[x_256][i]);

        samples_512[x_256][i] = samples_256[x_256][i];
        samples_512[y_256][i] = samples_256[y_256][i];
        samples_512[lt_256][i] = samples_256[lt_256][i];

        gen_int(samples_512[x_512][i], 8);
        gen_int(samples_512[y_512][i], 8);
    }

    return true;
}

const auto _ = init();
}  // namespace

template <>
const std::array<uint64_t, num_samples>& get_samples<uint64_t>(samples_set_id id) noexcept
{
    if (id != norm)
        std::abort();
    return samples_64_norm;
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

}  // namespace test
}  // namespace intx
