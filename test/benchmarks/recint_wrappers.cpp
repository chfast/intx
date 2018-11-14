// intx: extended precision integer library.
// Copyright 2018 Pawel Bylica.
// Licensed under the Apache License, Version 2.0. See the LICENSE file.

#include <ruint.h>

#include <intx/intx.hpp>

using namespace intx;

std::tuple<uint512, uint64_t> udivrem_1_64_recint(const uint512& u, uint64_t v) noexcept
{
    RecInt::ruint512 ru;
    std::memcpy(&ru.Low.Low.Low.Value, &u, sizeof(ru));

    RecInt::ruint512 rq;
    uint64_t r;

    RecInt::div(rq, r, ru, v);

    uint512 q;
    std::memcpy(&q.lo.lo, &rq, sizeof(q));
    return std::make_tuple(q, r);
};

std::tuple<uint512, uint512> udivrem_recint(const uint512& u, const uint512& v) noexcept
{
    RecInt::ruint512 ru;
    std::memcpy(&ru.Low.Low.Low.Value, &u, sizeof(ru));

    RecInt::ruint512 rv;
    std::memcpy(&rv.Low.Low.Low.Value, &v, sizeof(rv));

    RecInt::ruint512 rq;
    RecInt::ruint512 rr;

    RecInt::div(rq, rr, ru, rv);

    uint512 q;
    std::memcpy(&q.lo.lo, &rq, sizeof(q));
    uint512 r;
    std::memcpy(&r.lo.lo, &rr, sizeof(r));
    return std::make_tuple(q, r);
};

std::tuple<uint512, uint256> udivrem_recint(const uint512& u, const uint256& v) noexcept
{
    RecInt::ruint512 ru;
    std::memcpy(&ru.Low.Low.Low.Value, &u, sizeof(ru));

    RecInt::ruint256 rv;
    std::memcpy(&rv.Low.Low.Value, &v, sizeof(rv));

    RecInt::ruint512 rq;
    RecInt::ruint512 rr;

    RecInt::div(rq, rr, ru, RecInt::ruint512{rv});

    uint512 q;
    std::memcpy(&q.lo.lo, &rq, sizeof(q));
    uint256 r;
    std::memcpy(&r.lo, &rr, sizeof(r));
    return std::make_tuple(q, r);
};

std::tuple<uint512, uint128> udivrem_recint(const uint512& u, const uint128& v) noexcept
{
    RecInt::ruint512 ru;
    std::memcpy(&ru.Low.Low.Low.Value, &u, sizeof(ru));

    RecInt::ruint128 rv;
    std::memcpy(&rv.Low.Value, &v, sizeof(rv));

    RecInt::ruint512 rq;
    RecInt::ruint512 rr;

    RecInt::div(rq, rr, ru, RecInt::ruint512{RecInt::ruint256{rv}});

    uint512 q;
    std::memcpy(&q.lo.lo, &rq, sizeof(q));
    uint128 r;
    std::memcpy(&r, &rr, sizeof(r));
    return std::make_tuple(q, r);
};
