# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

set(INTX_INCLUDE_DIR ${PROJECT_SOURCE_DIR}/include)

add_library(int128 INTERFACE)
add_library(intx::int128 ALIAS int128)
target_compile_features(int128 INTERFACE cxx_std_14)
target_sources(int128 INTERFACE $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}/intx/int128.hpp>)
target_include_directories(int128 INTERFACE $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}>$<INSTALL_INTERFACE:include>)


add_library(intx STATIC
    ${INTX_INCLUDE_DIR}/intx/intx.hpp
    impl.cpp
)
add_library(intx::intx ALIAS intx)
target_compile_features(intx PUBLIC cxx_std_14)
target_include_directories(intx PUBLIC $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}>$<INSTALL_INTERFACE:include>)
target_link_libraries(intx PUBLIC intx::int128)

install(
    TARGETS intx int128
    EXPORT intxTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
install(
    DIRECTORY
    ${INTX_INCLUDE_DIR}/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
