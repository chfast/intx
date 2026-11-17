# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

if(CMAKE_CXX_COMPILER_ID MATCHES Clang AND CMAKE_CXX_COMPILER_FRONTEND_VARIANT STREQUAL GNU)
    # Built only by the test, with the flags of the build: clang -verify fails the compilation
    # if the diagnostics differ from the expected ones. The debug variant checks the assertions
    # (the "debug" prefix) and the release variant their absence, both with intx as a system
    # header, as its installed package provides it.
    foreach(variant debug release)
        set(target intx-diagnostics-${variant})
        add_library(${target} OBJECT EXCLUDE_FROM_ALL diagnostics.verify.cpp)
        target_link_libraries(${target} PRIVATE intx)
        target_include_directories(${target} SYSTEM PRIVATE ${INTX_INCLUDE_DIR})
        target_compile_options(
            ${target} PRIVATE
            -fsyntax-only -Xclang=-verify -Xclang=-verify-ignore-unexpected=note
        )
        set_target_properties(
            ${target} PROPERTIES
            COMPILE_WARNING_AS_ERROR OFF
            CXX_CLANG_TIDY ""
        )
    endforeach()
    target_compile_options(intx-diagnostics-debug PRIVATE -UNDEBUG -Xclang=-verify=debug)
    target_compile_definitions(intx-diagnostics-release PRIVATE NDEBUG)
    add_test(
        NAME ${PROJECT_NAME}/diagnostics
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --config $<CONFIG>
        --target intx-diagnostics-debug intx-diagnostics-release
    )
endif()
