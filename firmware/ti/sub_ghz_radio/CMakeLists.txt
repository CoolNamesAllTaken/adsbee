# Based on this Makefile: https://github.com/TexasInstruments/simplelink-prop_rf-examples/blob/main/examples/nortos/CC1312R1_LAUNCHXL/prop_rf/rfPacketRx/gcc/makefile

cmake_minimum_required(VERSION 3.16)

# Skip compiler checks.
set(CMAKE_C_COMPILER_WORKS 1)
set(CMAKE_CXX_COMPILER_WORKS 1)

project(sub_ghz_radio C CXX ASM)

message(STATUS "Current source directory: ${CMAKE_CURRENT_SOURCE_DIR}")
# Set the SimpleLink SDK path
set(SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR "$ENV{TI_LPF2_SDK_PATH}")
set(SYSCFG_OUTPUT_DIR "${CMAKE_CURRENT_SOURCE_DIR}/syscfg")
# Find ARM GCC compiler directory in /usr/local/
file(GLOB GCC_ARM_PATHS "/usr/local/gcc-arm-none-eabi-*")
if(GCC_ARM_PATHS)
    list(GET GCC_ARM_PATHS 0 GCC_ARMCOMPILER)
    message(STATUS "Found ARM GCC compiler: ${GCC_ARMCOMPILER}")
else()
    message(FATAL_ERROR "ARM GCC compiler not found in /usr/local/")
endif()

message(STATUS "SimpleLink SDK path: ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}")

# Create executable
add_executable(${PROJECT_NAME} main.cpp)

add_compile_definitions(DeviceFamily_CC13X2)
add_compile_definitions(ON_TI)

# Libraries to link
target_link_libraries(${PROJECT_NAME}
    PRIVATE
    # stdc++
    gcc # GCC runtime library
    c # C standard library
    m # Math library
)

# Include directories
target_include_directories(${PROJECT_NAME} PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/syscfg
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/posix
    $(GCC_ARMCOMPILER)/arm-none-eabi/include/newlib-nano
    $(GCC_ARMCOMPILER)/arm-none-eabi/include
    "/usr/local/gcc-arm-none-eabi-13.3.1/lib/gcc/arm-none-eabi/13.3.1/include"
)

target_sources(${PROJECT_NAME} PRIVATE
    # ${CMAKE_CURRENT_SOURCE_DIR}/rfPacketRx.c
    # ${CMAKE_CURRENT_SOURCE_DIR}/RFQueue.c
    ${CMAKE_CURRENT_SOURCE_DIR}/main.cpp
    ${SYSCFG_OUTPUT_DIR}/ti_devices_config.c
    ${SYSCFG_OUTPUT_DIR}/ti_drivers_config.c
    # ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/startup/startup_cc13x2_cc26x2_gcc.c 
)

add_subdirectory("/adsbee/common" ${CMAKE_BINARY_DIR}/adsbee_common)
add_subdirectory(${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR} ${CMAKE_BINARY_DIR}/ti_lpf2_sdk)

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
    --specs=nano.specs
    --specs=nosys.specs
)

# Add SimpleLink SDK libraries
target_link_directories(${PROJECT_NAME} PRIVATE
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos
    # "/usr/local/gcc-arm-none-eabi-13.3.1/lib/gcc/arm-none-eabi/13.3.1/thumb/v7e-m+fp/hard"
)

# # Custom command to create hex file
# add_custom_command(TARGET ${PROJECT_NAME} POST_BUILD
#     COMMAND ${CMAKE_OBJCOPY} -O ihex 
#     --remove-section .vtable 
#     --remove-section .dmaSpi0RxControlTableEntry 
#     --remove-section .dmaSpi0TxControlTableEntry 
#     --remove-section .dmaSpi1RxControlTableEntry 
#     --remove-section .dmaSpi1TxControlTableEntry 
#     --remove-section .dmaSpi0RxAltControlTableEntry 
#     --remove-section .dmaSpi0TxAltControlTableEntry 
#     --remove-section .dmaSpi1RxAltControlTableEntry 
#     --remove-section .dmaSpi1TxAltControlTableEntry 
#     --gap-fill 0xff 
#     ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME} ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}.hex
#     COMMENT "Creating hex file"
# )

# # GUI target
# add_custom_target(syscfg-gui
#     COMMAND ${SYSCONFIG_GUI_TOOL} ${SYSCFG_SOURCE}
#     COMMENT "Opening SysConfig GUI"
# )

