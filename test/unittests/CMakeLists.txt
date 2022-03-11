# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

include(GoogleTest)

hunter_add_package(GTest)
find_package(GTest CONFIG REQUIRED)

add_executable(intx-unittests
    test_bitwise.cpp
    test_builtins.cpp
    test_cases.hpp
    test_div.cpp
    test_int128.cpp
    test_intx.cpp
    test_intx_api.cpp
    test_suite.hpp
    test_uint256.cpp
)
target_link_libraries(intx-unittests PRIVATE intx intx::experimental intx::testutils GTest::gtest_main)
set_target_properties(intx-unittests PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)

gtest_add_tests(
    TARGET intx-unittests
    TEST_PREFIX ${PROJECT_NAME}/unittests/
    TEST_LIST unittests
    PROPERTIES
)
set_tests_properties(
    ${unittests} PROPERTIES
    ENVIRONMENT LLVM_PROFILE_FILE=${CMAKE_BINARY_DIR}/unittests-%p.profraw
)
