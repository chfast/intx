# intx: extended precision integer library.
# Copyright 2019-2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

add_library(intx STATIC
    ${INTX_INCLUDE_DIR}/intx/intx.hpp
    impl.cpp
)
add_library(intx::intx ALIAS intx)
target_compile_features(intx PUBLIC cxx_std_14)
target_include_directories(intx PUBLIC $<BUILD_INTERFACE:${INTX_INCLUDE_DIR}>$<INSTALL_INTERFACE:include>)
target_link_libraries(intx PUBLIC intx::int128)

install(
    TARGETS intx
    EXPORT intxTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
install(
    DIRECTORY
    ${INTX_INCLUDE_DIR}/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
