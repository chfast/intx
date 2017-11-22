cmake_minimum_required(VERSION 3.5)
list(APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake)

set(CMAKE_TOOLCHAIN_FILE ${CMAKE_SOURCE_DIR}/cmake/toolchains/default.cmake CACHE FILEPATH "CMake toolchain file")

set(HUNTER_CONFIGURATION_TYPES Release)
include(HunterGate)
HunterGate(
    URL "https://github.com/ruslo/hunter/archive/v0.19.167.tar.gz"
    SHA1 "244a13718ea2e6c0c8998d15559c7e459f615708"
)


project(intx)

add_subdirectory(libs/intx)

add_subdirectory(tests)

add_executable(int256 main.cpp)
target_link_libraries(int256 intx)