// intx: extended precision integer library.
// Copyright 2017 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <intx/intx.hpp>

using namespace intx;

static void udivrem_1_32_stable(uint32_t* q, uint32_t* r, const uint32_t* u, uint32_t v, int m)
{
    // Load the divisor once. The enabled more optimization because compiler
    // knows that divisor remains unchanged when storing to q[j].
    uint32_t remainder = 0;

    // TODO: Use fixed m, i.e. m = 8 for uint256.
    for (int j = m - 1; j >= 0; --j)
    {
        uint64_t dividend = join(remainder, u[j]);
        // This cannot overflow because the high part of the devidend is the
        // remainder of the previous division so smaller than v.
        std::tie(q[j], remainder) = udivrem_long(dividend, v);
    }
    *r = remainder;
}

std::tuple<uint512, uint32_t> udivrem_1_32_stable(const uint512& x, uint32_t y) noexcept
{
    uint512 q;
    uint32_t r;
    udivrem_1_32_stable(reinterpret_cast<uint32_t*>(&q), &r, reinterpret_cast<const uint32_t*>(&x),
        y, sizeof(uint512) / sizeof(uint32_t));
    return {q, r};
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

std::tuple<uint512, uint64_t> udivrem_1_64(const uint512& u, uint64_t v) noexcept
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
