# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_library(experimental STATIC)
add_library(intx::experimental ALIAS experimental)
target_compile_definitions(experimental PRIVATE INTX_EXPERIMENTAL)
target_include_directories(experimental PUBLIC ${PROJECT_SOURCE_DIR}/test)
target_link_libraries(experimental PUBLIC intx::intx)
target_sources(
    experimental PRIVATE
    add.cpp
    add.hpp
    addmod.hpp
    div.hpp
)
