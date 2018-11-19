# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

add_executable(intx-test
    test_div.cpp
    test_int128.cpp
    test_intx.cpp
    test_mul_full.cpp
    test_safe.cpp
    test_uint256_api.cpp
)
target_link_libraries(intx-test PRIVATE intx GTest::gtest GTest::main GMP::gmp)
set_target_properties(intx-test PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
