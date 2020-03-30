# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_library(experimental STATIC add.cpp add.hpp)
target_compile_definitions(experimental PRIVATE INTX_EXPERIMENTAL)
target_include_directories(experimental PUBLIC ${PROJECT_SOURCE_DIR}/test)
target_link_libraries(experimental PUBLIC intx::intx)
add_library(intx::experimental ALIAS experimental)
