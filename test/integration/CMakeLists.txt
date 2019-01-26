# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_executable(use-int128 use_int128.cpp)
target_link_libraries(use-int128 PRIVATE intx::int128)
