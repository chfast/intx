# intx: extended precision integer library.
# Copyright 2017 Pawel Bylica.
# Licensed under the Apache License, Version 2.0. See the LICENSE file.

include(GNUInstallDirs)

set(include_dir ${PROJECT_SOURCE_DIR}/include)

add_library(intx
    ${include_dir}/intx/int128.hpp
    ${include_dir}/intx/intx.hpp
    ${include_dir}/intx/mul_full.h
    ${include_dir}/intx/safe.hpp
    div.cpp
    div.hpp
    int128.cpp
    intx.cpp
)
target_include_directories(intx PUBLIC ${include_dir} ${CMAKE_CURRENT_SOURCE_DIR})

install(
    TARGETS intx
    EXPORT intxTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
install(
    DIRECTORY
    ${include_dir}/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
