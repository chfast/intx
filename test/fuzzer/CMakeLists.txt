# intx: extended precision integer library.
# Copyright 2018 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

string(REPLACE fuzzer-no-link fuzzer CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
add_executable(intx-fuzz-int128 fuzz_int128.cpp)
target_link_libraries(intx-fuzz-int128 PRIVATE intx)

add_executable(intx-fuzz-int512 fuzz_int512.cpp)
target_link_libraries(intx-fuzz-int512 PRIVATE intx GMP::gmp)

add_executable(intx-fuzz-safe fuzz_safe.cpp)
target_link_libraries(intx-fuzz-safe PRIVATE intx)
