
add_executable(intx-test
    test_intx.cpp
    test_safe.cpp
)
target_link_libraries(intx-test PRIVATE intx GTest::gtest GTest::main GMP::gmp)