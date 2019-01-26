# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

include(GNUInstallDirs)

set(include_dir ${PROJECT_SOURCE_DIR}/include)

add_library(int128 INTERFACE)
add_library(intx::int128 ALIAS int128)
target_sources(int128 INTERFACE ${include_dir}/intx/int128.hpp)
target_include_directories(int128 INTERFACE ${include_dir})


add_library(intx STATIC
    ${include_dir}/intx/intx.hpp
    ${include_dir}/intx/mul_full.h
    ${include_dir}/intx/safe.hpp
    div.cpp
    div.hpp
    intx.cpp
)
add_library(intx::intx ALIAS intx)
target_include_directories(intx PUBLIC ${include_dir} ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(intx PUBLIC intx::int128)

install(
    TARGETS intx int128
    EXPORT intxTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
install(
    DIRECTORY
    ${include_dir}/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
