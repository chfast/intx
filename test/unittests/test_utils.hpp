// intx: extended precision integer library.
// Copyright 2019-2020 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>

struct type_to_name
{
    template <typename T>
    static std::string GetName(int i);
};

template <>
inline std::string type_to_name::GetName<intx::uint128>(int)
{
    return "uint128";
}

template <>
inline std::string type_to_name::GetName<intx::uint256>(int)
{
    return "uint256";
}

template <>
inline std::string type_to_name::GetName<intx::uint512>(int)
{
    return "uint512";
}
