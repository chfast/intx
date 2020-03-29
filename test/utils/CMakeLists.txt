# intx: extended precision integer library.
# Copyright 2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_library(testutils STATIC EXCLUDE_FROM_ALL gmp.hpp random.cpp random.hpp)
add_library(intx::testutils ALIAS testutils)
target_include_directories(testutils PUBLIC ${PROJECT_SOURCE_DIR})
target_link_libraries(testutils PRIVATE intx::intx)
