// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <intx/intx.hpp>
#include <string>

struct type_to_name
{
    template <typename T>
    static std::string GetName(int i)
    {
        if (std::is_same<T, intx::uint128>())
            return "uint128";
        if (std::is_same<T, intx::uint256>())
            return "uint256";
        if (std::is_same<T, intx::uint512>())
            return "uint512";

        return std::to_string(i);
    }
};
