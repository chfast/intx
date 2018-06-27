// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

using namespace intx;

std::tuple<uint256, uint32_t> udivrem_1_32_long(const uint256& u, uint32_t v) noexcept
{
    static constexpr int num_words = sizeof(uint256) / sizeof(uint32_t);

    uint256 q;
    auto* q_words = reinterpret_cast<uint32_t*>(&q);
    auto* u_words = reinterpret_cast<const uint32_t*>(&u);

    uint32_t reminder = 0;
    const uint32_t divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udivrem_long(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}

std::tuple<uint256, uint32_t> udivrem_1_32_unr(const uint256& u, uint32_t v) noexcept
{
    static constexpr int num_words = sizeof(uint256) / sizeof(uint32_t);

    uint256 q;
    uint32_t* q_words = reinterpret_cast<uint32_t*>(&q);
    const uint32_t* u_words = reinterpret_cast<const uint32_t*>(&u);

    uint32_t reminder = 0;
    const uint64_t divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udiv_qr_unr(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}

std::tuple<uint512, uint32_t> udivrem_1_32_long(const uint512& u, uint32_t v) noexcept
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    uint512 q;
    auto* q_words = reinterpret_cast<uint32_t*>(&q);
    auto* u_words = reinterpret_cast<const uint32_t*>(&u);

    uint32_t reminder = 0;
    const uint32_t divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udivrem_long(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}

std::tuple<uint512, uint32_t> udivrem_1_32_unr(const uint512& u, uint32_t v) noexcept
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint32_t);

    uint512 q;
    uint32_t* q_words = reinterpret_cast<uint32_t*>(&q);
    const uint32_t* u_words = reinterpret_cast<const uint32_t*>(&u);

    uint32_t reminder = 0;
    const uint64_t divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udiv_qr_unr(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}

std::tuple<uint512, uint64_t> udivrem_1_64_long(const uint512& u, uint64_t v) noexcept
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint64_t);

    uint512 q;
    uint64_t* q_words = reinterpret_cast<uint64_t*>(&q);
    const uint64_t* u_words = reinterpret_cast<const uint64_t*>(&u);

    uint64_t reminder = 0;
    const uint64_t divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udivrem_long(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}


// TODO: Slow on clang, fast on GCC.
std::tuple<uint512, uint64_t> udivrem_1_64_unr(const uint512& u, uint64_t v) noexcept
{
    static constexpr int num_words = sizeof(uint512) / sizeof(uint64_t);

    uint512 q;
    uint64_t* q_words = reinterpret_cast<uint64_t*>(&q);
    const uint64_t* u_words = reinterpret_cast<const uint64_t*>(&u);

    uint64_t reminder = 0;
    const uint128 divisor = v;

    for (int j = num_words - 1; j >= 0; --j)
        std::tie(q_words[j], reminder) = udiv_qr_unr(join(reminder, u_words[j]), divisor);

    return {q, reminder};
}

