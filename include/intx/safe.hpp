// Copyright 2017 Pawel Bylica.
// Governed by the Apache License, Version 2.0. See the LICENSE file.

#pragma once

#include <limits>
#include <stdexcept>

namespace intx
{
enum class status : char
{
    normal = 0,
    plus_infinity,
    minus_infinity,
    invalid
};

class bad_operation : public std::exception
{};

template<typename Int>
struct safe
{
    static constexpr auto max_value = std::numeric_limits<Int>::max();
    static constexpr auto min_value = std::numeric_limits<Int>::min();

    safe() noexcept = default;

    constexpr safe(Int value) noexcept
        : m_value(value)
    {}

    constexpr explicit safe(status st) noexcept
        : m_status(st)
    {}

    Int value() const
    {
        // FIXME: throw if not valid?
        return m_value;
    }

    bool valid() const noexcept { return m_status == status::normal; }
    status get_status() const noexcept { return m_status; }

private:
    Int m_value = 0;
    status m_status = status::normal;
};

template<typename Int>
safe<Int> add(safe<Int> a, safe<Int> b)
{
    if (b.value() >= 0)
    {
        if (a.value() > safe<Int>::max_value - b.value())
            return safe<Int>{status::plus_infinity};
    }
    else
    {
        if (a.value() < safe<Int>::min_value - b.value())
            return safe<Int>{status::plus_infinity};
    }
    return a.value() + b.value();
}

template<typename Int>
safe<Int> operator+(safe<Int> a, safe<Int> b)
{
    // This implementation is much smaller and faster.
    Int s;
    if (__builtin_add_overflow(a.value(), b.value(), &s))
        return safe<Int>{status::plus_infinity};
    return s;
}

template<typename Int>
bool operator==(safe<Int> a, safe<Int> b)
{
    if (a.valid() && b.valid())
        return a.value() == b.value();
    return false;  // TODO: Is it ok?
}

template<typename Int>
bool operator==(safe<Int> a, Int b)
{
    if (a.valid())
        return a.value() == b;
    return false;  // TODO: Is it ok?
}

template<typename Int>
bool operator!=(safe<Int> a, safe<Int> b) { return !(a == b); }

template<typename Int>
bool operator<(safe<Int> a, safe<Int> b)
{
    switch (a.get_status())
    {
    case status::normal:
        switch (b.get_status())
        {
        case status::normal:
            return a.value() < b.value();
        case status::plus_infinity:
            return true;
        case status::minus_infinity:
            return false;
        case status::invalid:
            throw bad_operation{};
        }
    case status::plus_infinity:
        switch (b.get_status())
        {
        case status::normal:
            return false;
        case status::plus_infinity:
            throw bad_operation{};
        case status::minus_infinity:
            return false;
        case status::invalid:
            throw bad_operation{};
        }
    case status::minus_infinity:
        switch (b.get_status())
        {
        case status::normal:
            return true;
        case status::plus_infinity:
            return true;
        case status::minus_infinity:
            throw bad_operation{};
        case status::invalid:
            throw bad_operation{};
        }
    default:
        throw bad_operation{};
    }
}

template<typename Int>
bool operator<=(safe<Int> a, safe<Int> b) { return a < b || a == b; }

template<typename Int>
bool operator>=(safe<Int> a, safe<Int> b) { return !(a < b); }

template<typename Int>
bool operator>(safe<Int> a, safe<Int> b) { return !(a <= b); }

using safe_int = safe<int>;

template safe_int operator+<int>(safe_int a, safe_int b);
template safe_int add<int>(safe_int a, safe_int b);

}
