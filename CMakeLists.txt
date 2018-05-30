cmake_minimum_required(VERSION 3.5)
list(APPEND CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake)

set(CMAKE_TOOLCHAIN_FILE ${CMAKE_SOURCE_DIR}/cmake/toolchains/default.cmake CACHE FILEPATH "CMake toolchain file")

set(HUNTER_CONFIGURATION_TYPES Release
    CACHE STRING "Build type of the Hunter packages")
set(HUNTER_CACHE_SERVERS
    "https://github.com/ethereum/hunter-cache"
    CACHE STRING "Hunter cache servers")
include(HunterGate)
HunterGate(
    URL "https://github.com/ruslo/hunter/archive/v0.19.167.tar.gz"
    SHA1 "244a13718ea2e6c0c8998d15559c7e459f615708"
)


project(intx)

# FIXME: Add back -Wconversion, test with clang.
add_compile_options(-Werror -Wall -Wextra)
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-omit-frame-pointer -fsanitize=address")

add_subdirectory(libs/intx)

add_subdirectory(tests)