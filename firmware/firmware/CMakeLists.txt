cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(pico_sdk_import.cmake)

project(ads_bee_project C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)

if (PICO_SDK_VERSION_STRING VERSION_LESS "1.3.0")
    message(FATAL_ERROR "Raspberry Pi Pico SDK version 1.3.0 (or later) required. Your version is ${PICO_SDK_VERSION_STRING}")
endif()

# Initialize the SDK
pico_sdk_init()

add_compile_options(
    -Wall
    -Wno-format          # int != int32_t as far as the compiler is concerned because gcc has int32_t as long int
    -Wno-unused-function # we have some for the docs that aren't called
    -Wno-maybe-uninitialized
)

# Source files are added with target_sources in subdirectories
add_executable(ads_bee "")

add_subdirectory(src)
add_subdirectory(inc)

# In case there are files directly in src and inc
target_include_directories(ads_bee PRIVATE 
    src
    inc
)

# Firmware: Create map/bin/hex file etc
pico_add_extra_outputs(ads_bee)
pico_enable_stdio_usb(ads_bee 1) # use USB for standard printing
pico_enable_stdio_uart(ads_bee 0) # disable STDIO UART

# Firmware: Pull in Pico library
target_link_libraries(ads_bee 
    pico_stdlib
    pico_float # for math functions
    hardware_pwm
    hardware_adc
)
