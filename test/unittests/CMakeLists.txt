# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

hunter_add_package(GTest)
find_package(GTest CONFIG REQUIRED)

add_executable(intx-test
    test_cases.hpp
    test_div.cpp
    test_int128.cpp
    test_intx.cpp
    test_intx_api.cpp
)
target_link_libraries(intx-test PRIVATE intx GTest::gtest GTest::main)
set_target_properties(intx-test PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
