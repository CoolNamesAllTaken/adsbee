# Based on this Makefile: https://github.com/TexasInstruments/simplelink-prop_rf-examples/blob/main/examples/nortos/CC1312R1_LAUNCHXL/prop_rf/rfPacketRx/gcc/makefile

cmake_minimum_required(VERSION 3.16)
set(TI_MIN_CMAKE_VERSION 3.16)

message(STATUS "Current source directory: ${CMAKE_CURRENT_SOURCE_DIR}")
# Set the SimpleLink SDK path
set(SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR "$ENV{TI_LPF2_SDK_PATH}" CACHE PATH "ti-lpf2 SDK install dir.")
set(SYSCFG_OUTPUT_DIR "${CMAKE_CURRENT_SOURCE_DIR}/syscfg" CACHE PATH "dir where all the sysconfig output goes.")
set(CMAKE_COMMON_INSTALL_DIR ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source/cmake/scripts/cmake-common CACHE PATH "cmake-common scripts dir from the LPF2 SDK.")
set(CMAKE_TOOLCHAIN_FILE ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source/cmake/toolchains/gcc.cmake)
message(STATUS "SimpleLink SDK path: ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}")

# Find ARM GCC compiler directory in /usr/local/
file(GLOB GCC_ARM_PATHS "/usr/local/gcc-arm-none-eabi-*")
if(GCC_ARM_PATHS)
    list(GET GCC_ARM_PATHS 0 GCC_ARMCOMPILER)
    message(STATUS "Found ARM GCC compiler: ${GCC_ARMCOMPILER}")
else()
    message(FATAL_ERROR "ARM GCC compiler not found in /usr/local/")
endif()
# Extract the GCC ARM compiler version from the path
string(REGEX MATCH "gcc-arm-none-eabi-([0-9]+\\.[0-9]+\\.[0-9]+)" _ ${GCC_ARMCOMPILER})
set(GCC_ARM_VERSION ${CMAKE_MATCH_1})
message(STATUS "ARM GCC compiler version: ${GCC_ARM_VERSION}")

# Skip compiler checks.
# set(CMAKE_C_COMPILER_WORKS 1)
# set(CMAKE_CXX_COMPILER_WORKS 1)

# Compile definitions need to be defined before the target!
add_compile_definitions(DeviceFamily_CC13X2)
# add_compile_definitions(DeviceFamily_CC13X2_CC26X2)
add_compile_definitions(ON_TI)

project(sub_ghz_radio C CXX ASM)



# Create executable
add_executable(${PROJECT_NAME}
    main.cpp
)
set_target_properties(${PROJECT_NAME} PROPERTIES
    OUTPUT_NAME "${PROJECT_NAME}.elf"
)

# Link against the M4 hard float toolchain
# target_link_libraries(your_app PRIVATE CMakeCommon::gcc_m4f)

# Include directories
target_include_directories(${PROJECT_NAME} PRIVATE
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/posix
    $(GCC_ARMCOMPILER)/lib/gcc/arm-none-eabi/${GCC_ARM_VERSION}/include # For arm_acle.h
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/syscfg
    ${CMAKE_CURRENT_SOURCE_DIR}/smartrf
)

# Libraries to link
target_link_libraries(${PROJECT_NAME}
    PRIVATE
    # stdc++
    # gcc # GCC runtime library
    # c # C standard library
    # m # Math library
    CMakeCommon::gcc_m4f # Use TI gcc toolchain for ARM M4 with hardware floating point.
    # Assume default library install locations (within /usr/local/ti-lpf2-sdk).
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/lib/gcc/m4f/nortos_cc13x2.a
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/build/gcc/source/ti/log/lib/gcc/m4f/log_cc13x2/log_cc13x2.a
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/build/gcc/source/ti/drivers/lib/gcc/m4f/drivers_cc13x2/drivers_cc13x2.a
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/build/gcc/source/ti/devices/cc13x2_cc26x2/lib/gcc/m4f/driverlib/driverlib.lib
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source/ti/drivers/rf/lib/gcc/m4f/rf_multiMode_cc13x2.a
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source/ti/grlib/lib/gcc/m4f/grlib.a
)

set(TI_LINKER_COMMAND_FILE "${CMAKE_CURRENT_SOURCE_DIR}/cc13x2_cc26x2_nortos.lds")

target_sources(${PROJECT_NAME} PRIVATE
    syscalls_stub.c
    # ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/NoRTOS.c
    NoRTOS.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/rfPacketRx.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/RFQueue.cpp
    ${SYSCFG_OUTPUT_DIR}/ti_devices_config.c
    ${SYSCFG_OUTPUT_DIR}/ti_drivers_config.c
    ${CMAKE_CURRENT_SOURCE_DIR}/smartrf/smartrf_settings.c
)

add_subdirectory("/adsbee/common" ${CMAKE_BINARY_DIR}/adsbee_common)
# Do NOT add the SDK itself as a subdirectory or else it will assume you are building the SDK and take over a bunch of important variables like CMAKE_COMMON_INSTALL_DIR.

# Compiler flags
target_compile_options(${PROJECT_NAME} PRIVATE
    -mcpu=cortex-m4
    -march=armv7e-m
    -mthumb
    -mfloat-abi=hard
    -mfpu=fpv4-sp-d16
    -ffunction-sections
    -fdata-sections
    -g
    -gstrict-dwarf
    -Wall
    # -O0
)

# Linker script
set(LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/cc13x2_cc26x2_nortos.lds")

# Linker flags
target_link_options(${PROJECT_NAME} PRIVATE
    -T${LINKER_SCRIPT}
    -Wl,-Map=${PROJECT_NAME}.map
    -eresetISR
    -march=armv7e-m
    -mthumb
    -mfloat-abi=hard
    -mfpu=fpv4-sp-d16
    -nostartfiles
    -static
    -Wl,--gc-sections
    --specs=nosys.specs
)

# Custom command to create binary file
add_custom_command(TARGET ${PROJECT_NAME} POST_BUILD
    COMMAND arm-none-eabi-objcopy -O binary 
    --gap-fill 0xff 
    ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}.elf ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}.bin
    COMMENT "Creating binary file"
)

