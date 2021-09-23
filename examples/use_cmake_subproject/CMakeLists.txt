# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

# This example shows how to use intx CMake subproject.

cmake_minimum_required(VERSION 3.10)

project(use_intx_cmake_subproject LANGUAGES CXX)

add_subdirectory(intx)

add_executable(use_intx use_intx.cpp)
target_link_libraries(use_intx PRIVATE intx::intx)
