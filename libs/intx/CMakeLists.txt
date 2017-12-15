
add_library(
    intx
    intx.hpp
    intx.cpp
    mul.h
    div.h
)
target_include_directories(intx PUBLIC ${CMAKE_SOURCE_DIR}/include ${CMAKE_CURRENT_SOURCE_DIR})