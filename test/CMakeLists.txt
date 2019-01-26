# intx: extended precision integer library.
# Copyright 2019 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

hunter_add_package(GTest)
find_package(GTest CONFIG REQUIRED)

hunter_add_package(benchmark)
find_package(benchmark CONFIG REQUIRED)

find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_library(GMP_LIBRARY NAMES gmp)

message(STATUS "GMP: ${GMP_LIBRARY} (${GMP_INCLUDE_DIR})")
add_library(GMP::gmp IMPORTED SHARED)
set_property(TARGET GMP::gmp PROPERTY IMPORTED_CONFIGURATIONS Release)
set_property(TARGET GMP::gmp PROPERTY IMPORTED_LOCATION_RELEASE ${GMP_LIBRARY})
set_property(TARGET GMP::gmp PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${GMP_INCLUDE_DIR})

add_subdirectory(benchmarks)
add_subdirectory(integration)
add_subdirectory(unittests)

if(INTX_FUZZING)
    add_subdirectory(fuzzer)
endif()
