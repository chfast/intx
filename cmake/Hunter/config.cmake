# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

hunter_config(
    GTest
    VERSION 1.10.0
    URL https://github.com/google/googletest/archive/release-1.10.0.tar.gz
    SHA1 9c89be7df9c5e8cb0bc20b3c4b39bf7e82686770
    CMAKE_ARGS BUILD_GMOCK=OFF gtest_force_shared_crt=ON
)
