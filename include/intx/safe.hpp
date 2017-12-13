// Copyright 2017 Pawel Bylica
// Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0)

#pragma once

#include <limits>

namespace intx
{
template<typename Int>
struct safe
{
    static constexpr auto max_value = std::numeric_limits<Int>::max();
    static constexpr auto min_value = std::numeric_limits<Int>::min();

    safe() noexcept = default;

    constexpr safe(Int value) noexcept
        : m_value(value)
    {}

    static safe invalid() { safe i; i.m_invalid = true; return i; }

    Int value() const
    {
        // FIXME: throw if not valid?
        return m_value;
    }

    bool valid() const noexcept { return !m_invalid; }

private:
    Int m_value = 0;
    bool m_invalid = false;
};

template<typename Int>
safe<Int> add(safe<Int> a, safe<Int> b)
{
    if (b.value() >= 0)
    {
        if (a.value() > safe<Int>::max_value - b.value())
            return safe<Int>::invalid();
    }
    else
    {
        if (a.value() < safe<Int>::min_value - b.value())
            return safe<Int>::invalid();
    }
    return a.value() + b.value();
}

template<typename Int>
safe<Int> operator+(safe<Int> a, safe<Int> b)
{
    // This implementation is much smaller and faster.
    Int s;
    if (__builtin_add_overflow(a.value(), b.value(), &s))
        return safe<Int>::invalid();
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

using safe_int = safe<int>;

template safe_int operator+<int>(safe_int a, safe_int b);
template safe_int add<int>(safe_int a, safe_int b);

}
