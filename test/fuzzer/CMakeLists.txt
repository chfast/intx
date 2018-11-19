# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=fuzzer,undefined")
add_executable(intx-fuzz-int128 fuzz_int128.cpp)
target_link_libraries(intx-fuzz-int128 PRIVATE intx)
target_compile_options(intx-fuzz-int128 PRIVATE -fsanitize=fuzzer,undefined)

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=fuzzer,undefined")
add_executable(intx-fuzz-int512 fuzz_int512.cpp)
target_link_libraries(intx-fuzz-int512 PRIVATE intx GMP::gmp)
target_compile_options(intx-fuzz-int512 PRIVATE -fsanitize=fuzzer,undefined)

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=fuzzer,undefined")
add_executable(intx-fuzz-safe fuzz_safe.cpp)
target_link_libraries(intx-fuzz-safe PRIVATE intx)
target_compile_options(intx-fuzz-safe PRIVATE -fsanitize=fuzzer,undefined)
