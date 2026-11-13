// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.
#pragma once

#include <gtest/gtest.h>
#include <intx/intx.hpp>

#if __cpp_exceptions
    #define EXPECT_THROW_MESSAGE(stmt, ex_type, expected)                                        \
        try                                                                                      \
        {                                                                                        \
            stmt;                                                                                \
            ADD_FAILURE() << "Exception of type " #ex_type " is expected, but none was thrown."; \
        }                                                                                        \
        catch (const ex_type& exception)                                                         \
        {                                                                                        \
            EXPECT_STREQ(exception.what(), expected);                                            \
        }                                                                                        \
        (void)0
#else
    #define EXPECT_THROW_MESSAGE(stmt, ex_type, expected) EXPECT_DEATH(stmt, expected)
#endif


struct type_to_name
{
    template <typename T>
    static std::string GetName([[maybe_unused]] int i)
    {
        return "uint" + std::to_string(T::num_bits);
    }
};

template <typename T>
class uint_test : public testing::Test
{
};

using test_types =
    testing::Types<intx::uint128, intx::uint192, intx::uint256, intx::uint384, intx::uint512>;
TYPED_TEST_SUITE(uint_test, test_types, type_to_name);
