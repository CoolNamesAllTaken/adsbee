cmake_minimum_required(VERSION 3.13)

# Flag indicating that build is not for the embedded target. Used to toggle target_source calls.
set(CROSS_COMPILED 1)

project(ads_bee_project C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

set(CMAKE_BUILD_TYPE Debug) # add debug symbols (use RelWithDebInfo instead to add optimization)

add_compile_options(
    -Wall
    -Wno-format          # int != int32_t as far as the compiler is concerned because gcc has int32_t as long int
    -Wno-unused-function # we have some for the docs that aren't called
    -Wno-maybe-uninitialized
)

# Source files are added with target_sources in subdirectories
add_executable(ads_bee_test "")

# Add subdirectories after creating the target so that CMake doesn't get upset.
add_subdirectory(/ads_bee/firmware/src firmware/src) # maps firmware src folder to local firmware/src
add_subdirectory(/ads_bee/firmware/inc firmware/inc) # maps firmware inc folder to local firmware/inc
add_subdirectory(src)
add_subdirectory(inc)

# In case there are files directly in src and inc
target_include_directories(ads_bee_test PRIVATE 
    src
    inc
)

# Test: Pull in google test library
add_library(libgtest SHARED IMPORTED)
set_target_properties(libgtest PROPERTIES IMPORTED_LOCATION /ads_bee/modules/googletest/build/lib/libgtest.so)
target_link_libraries(ads_bee_test PRIVATE libgtest)