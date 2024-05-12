cmake_minimum_required(VERSION 3.13)

# Pull in SDK (must be before project)
include(pico_sdk_import.cmake)

project(ads_bee C CXX ASM)
set(CMAKE_C_STANDARD 17)
set(CMAKE_CXX_STANDARD 20)

# Force -00 optimization during debug to try fixing JLink issues.
# SET(CMAKE_CXX_FLAGS_DEBUG "-O0")
# SET(CMAKE_C_FLAGS_DEBUG "-O0")

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
add_executable(${PROJECT_NAME} "")

add_subdirectory(src)

# In case there are files directly in src and inc
target_include_directories(${PROJECT_NAME} PRIVATE 
    src
    /ads_bee/modules/cppAT/src
)

target_sources(${PROJECT_NAME} PRIVATE
    /ads_bee/modules/cppAT/src/cpp_at.cc
    # /ads_bee/modules/cppAT/src/cpp_at.hh
)

# Create C header file with the name <pio program>.pio.h
pico_generate_pio_header(${PROJECT_NAME}  
        ${CMAKE_CURRENT_LIST_DIR}/pio/blink.pio 
)
pico_generate_pio_header(${PROJECT_NAME}  
        ${CMAKE_CURRENT_LIST_DIR}/pio/capture.pio       
)

# Firmware: Pull in Pico library
target_link_libraries(${PROJECT_NAME} 
    pico_stdlib
    pico_float # for math functions
    hardware_pio
    hardware_pwm
    hardware_adc
)

# Firmware: Create map/bin/hex file etc
pico_add_extra_outputs(${PROJECT_NAME})

# Set up debug USB
pico_enable_stdio_usb(${PROJECT_NAME} 1) # use USB for standard printing
pico_enable_stdio_uart(${PROJECT_NAME} 0) # disable STDIO UART
