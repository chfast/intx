# intx: extended precision integer library.
# Copyright 2025 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

# This example shows how to use intx Conan package.

cmake_minimum_required(VERSION 3.10)

project(use_intx_conan_package LANGUAGES CXX)

find_package(intx CONFIG REQUIRED)

add_executable(use_intx ../../../examples/use_cmake_package/use_intx.cpp)
target_link_libraries(use_intx PRIVATE intx::intx)
