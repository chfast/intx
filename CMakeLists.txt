cmake_minimum_required(VERSION 3.5)
project(intx)

set(CMAKE_CXX_STANDARD 11)

add_subdirectory(libs/intx)

add_executable(int256 main.cpp)
target_link_libraries(int256 intx)