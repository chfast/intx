# intx: extended precision integer library.
# Copyright 2022 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_library(analysis OBJECT)
target_link_libraries(analysis PRIVATE intx)
target_sources(
    analysis PRIVATE
    add.cpp
    div.cpp
    lt.cpp
    sub.cpp
)
