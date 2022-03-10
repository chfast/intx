// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

/// @file
/// Helpers for generating random inputs for benchmarks.

#include <algorithm>
#include <array>
#include <iterator>
#include <random>

namespace intx::test
{
using seed_type = std::random_device::result_type;

inline seed_type get_seed()
{
    return 2358091149;
}

/// Linear congruential generator for any integer type.
template <typename Int>
struct lcg
{
    Int state = 0;

    explicit lcg(seed_type seed) : state{seed}
    {
        // Run for some time to fill the state.
        for (int i = 0; i < 97; ++i)
            (*this)();
    }

    Int operator()()
    {
        return state = static_cast<Int>(Int{0x5851f42d4c957f2d} * state + Int{0x14057b7ef767814f});
    }
};


inline std::vector<uint64_t> gen_uniform_seq(size_t num)
{
    std::mt19937_64 rng{get_seed()};
    std::uniform_int_distribution<uint64_t> dist;
    std::vector<uint64_t> seq;
    std::generate_n(std::back_inserter(seq), num, [&] { return dist(rng); });
    return seq;
}

/// The number of samples in samples sets.
/// The value is selected to stay in L1 cache, i.e. 32*1024 / (2 * 512 / 8) == 256.
/// However, the bigger values increase execution time only slightly, so the value
/// may be increased if that's over better samples distribution.
constexpr size_t num_samples = 256;

enum samples_set_id
{
    x_64,    ///< Set of random samples with ~64 (1 word) significant bits.
    x_128,   ///< Set of random samples with ~128 (2 words) significant bits.
    x_192,   ///< Set of random samples with ~192 (3 words) significant bits.
    x_256,   ///< Set of random samples with ~256 (4 words) significant bits.
    y_256,   ///< Set of random samples with ~256 (4 words) significant bits, different from x_256.
    lt_256,  ///< Set of random samples where each lt_256[i] <= x_256[i] && lt_256[i] <= y_256[i].
    lt_x_256,  ///< Set of random samples where each lt_x_256[i] <= x_256[i].
    x_512,     ///< Set of random samples with ~512 (8 words) significant bits.
    y_512,  ///< Set of random samples with ~512 (8 words) significant bits, different from x_512.
    norm,   ///< Set of random samples of normalized (first bit set) values.
    shift_w0,
    shift_w1,
    shift_w2,
    shift_w3,
    shift_mixed,
};

template <typename T>
const std::array<T, num_samples>& get_samples(samples_set_id id) noexcept;


}  // namespace intx::test
