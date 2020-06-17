# intx: extended precision integer library.
# Copyright 2020 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

# Test suite for using intx as a CMake subproject.

# All files needed to build intx as a CMake subproject:
file(
    COPY
    ${PROJECT_SOURCE_DIR}/CMakeLists.txt
    ${PROJECT_SOURCE_DIR}/cmake
    ${PROJECT_SOURCE_DIR}/include
    DESTINATION ${PROJECT_SOURCE_DIR}/examples/use_cmake_subproject/intx
)

set(build_dir ${CMAKE_CURRENT_BINARY_DIR}/build)
file(MAKE_DIRECTORY ${build_dir})

if(CMAKE_BUILD_TYPE)
    set(build_type_arg -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE})
endif()

add_test(
    NAME ${PROJECT_NAME}/cmake_subproject/use_cmake_subproject
    COMMAND
    ${CMAKE_COMMAND} -G ${CMAKE_GENERATOR}
    ${PROJECT_SOURCE_DIR}/examples/use_cmake_subproject
    ${build_type_arg}
    WORKING_DIRECTORY ${build_dir}
)
