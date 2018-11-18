# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=fuzzer,undefined")
add_executable(intx-fuzz-int128 fuzz_int128.cpp)
target_link_libraries(intx-fuzz-int128 PRIVATE intx)
target_compile_options(intx-fuzz-int128 PRIVATE -fsanitize=fuzzer,undefined)
