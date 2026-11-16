# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.

if(CMAKE_CXX_COMPILER_ID MATCHES Clang AND CMAKE_CXX_COMPILER_FRONTEND_VARIANT STREQUAL GNU)
    # Built only by the test, with the flags of the build: clang -verify fails the compilation
    # if the diagnostics differ from the expected ones.
    add_library(intx-diagnostics OBJECT EXCLUDE_FROM_ALL diagnostics.verify.cpp)
    target_link_libraries(intx-diagnostics PRIVATE intx)
    target_compile_options(
        intx-diagnostics PRIVATE
        -fsyntax-only -Xclang=-verify -Xclang=-verify-ignore-unexpected=note
    )
    # The extensions make __int128 an integral type also in libstdc++ before 16.
    set_target_properties(
        intx-diagnostics PROPERTIES
        CXX_EXTENSIONS ON
        COMPILE_WARNING_AS_ERROR OFF
        CXX_CLANG_TIDY ""
    )
    add_test(
        NAME ${PROJECT_NAME}/diagnostics
        COMMAND ${CMAKE_COMMAND} --build ${CMAKE_BINARY_DIR} --config $<CONFIG> --target intx-diagnostics
    )
endif()
