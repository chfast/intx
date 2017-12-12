
add_executable(intx-test mul.cpp)
target_link_libraries(intx-test PRIVATE intx GTest::gtest GTest::main GMP::gmp)