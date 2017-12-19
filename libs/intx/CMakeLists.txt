
set(include_dir ${CMAKE_SOURCE_DIR}/include)

add_library(
    intx
    ${include_dir}/intx/safe.hpp
    intx.hpp
    intx.cpp
    mul.h
    div.h
)
target_include_directories(intx PUBLIC ${include_dir} ${CMAKE_CURRENT_SOURCE_DIR})