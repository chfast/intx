# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

find_package(GMP REQUIRED)

string(REPLACE fuzzer-no-link fuzzer CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})

add_executable(intx-fuzzer fuzz_intx.cpp)
target_link_libraries(intx-fuzzer PRIVATE intx GMP::gmp)

add_executable(opmod-fuzzer opmod_fuzz.cpp)
target_link_libraries(opmod-fuzzer PRIVATE intx GMP::gmp)
target_compile_features(opmod-fuzzer PRIVATE cxx_std_20)

set_target_properties(intx-fuzzer opmod-fuzzer PROPERTIES RUNTIME_OUTPUT_DIRECTORY ..)
