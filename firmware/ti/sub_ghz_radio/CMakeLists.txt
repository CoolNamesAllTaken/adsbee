# cmake_minimum_required(VERSION 3.13)

# set(CMAKE_C_STANDARD 17)
# set(CMAKE_CXX_STANDARD 20)

# project(adsbee_uat C CXX ASM)

# add_executable(adsbee_uat main.cc)

# # Pull in SDK (must be before project)
# add_subdirectory(${TI_LPF2_SDK_PATH})

cmake_minimum_required(VERSION 3.16)

# Skip compiler checks.
set(CMAKE_C_COMPILER_WORKS 1)
set(CMAKE_CXX_COMPILER_WORKS 1)

project(sub_ghz_radio C CXX ASM)

message(STATUS "Current source directory: ${CMAKE_CURRENT_SOURCE_DIR}")
# Set the SimpleLink SDK path
set(SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR "$ENV{TI_LPF2_SDK_PATH}")
set(SYSCFG_OUTPUT_DIR "${CMAKE_CURRENT_SOURCE_DIR}/syscfg")

# # SysConfig setup
# set(SYSCONFIG_TOOL "$ENV{SYSCONFIG_TOOL}" CACHE FILEPATH "Path to SysConfig tool")
# get_filename_component(SYSCONFIG_DIR ${SYSCONFIG_TOOL} DIRECTORY)
# set(SYSCONFIG_GUI_TOOL "${SYSCONFIG_DIR}/sysconfig_gui${CMAKE_EXECUTABLE_SUFFIX}" CACHE FILEPATH "Path to SysConfig GUI tool")

# # Generate SysConfig files
# set(SYSCFG_SOURCE ${CMAKE_CURRENT_SOURCE_DIR}/../rfPacketRx.syscfg)
# set(SYSCFG_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/syscfg)
# add_custom_command(
#     OUTPUT ${SYSCFG_OUTPUT_DIR}/ti_devices_config.c ${SYSCFG_OUTPUT_DIR}/ti_drivers_config.c
#     COMMAND ${SYSCONFIG_TOOL} --compiler gcc --product ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/.metadata/product.json --output ${SYSCFG_OUTPUT_DIR} ${SYSCFG_SOURCE}
#     DEPENDS ${SYSCFG_SOURCE}
#     COMMENT "Generating SysConfig files"
# )

# Set source files
# set(SOURCE_FILES
    
# )

message(STATUS "SimpleLink SDK path: ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}")

# Create executable
add_executable(${PROJECT_NAME} main.cc)

add_compile_definitions(DeviceFamily_CC13X2)
add_compile_definitions(ON_TI)

# Include directories
target_include_directories(${PROJECT_NAME} PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/syscfg
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos/posix
)

target_sources(${PROJECT_NAME} PRIVATE
    # ${CMAKE_CURRENT_SOURCE_DIR}/rfPacketRx.c
    # ${CMAKE_CURRENT_SOURCE_DIR}/RFQueue.c
    ${CMAKE_CURRENT_SOURCE_DIR}/main.cc
    # ${SYSCFG_OUTPUT_DIR}/ti_devices_config.c
    # ${SYSCFG_OUTPUT_DIR}/ti_drivers_config.c
)

add_subdirectory("/adsbee/common" ${CMAKE_BINARY_DIR}/adsbee_common)

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
)

# Linker script
set(LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/cc13x2_cc26x2_nortos.lds")

# Linker flags
target_link_options(${PROJECT_NAME} PRIVATE
    -T${LINKER_SCRIPT}
    -Wl,-Map=${PROJECT_NAME}.map
    # -eresetISR
    -march=armv7e-m
    -mthumb
    -mfloat-abi=hard
    -mfpu=fpv4-sp-d16
    -nostartfiles
    -static
    -Wl,--gc-sections
    # --specs=nano.specs
    # --specs=nosys.specs
)

# Add SimpleLink SDK libraries
target_link_directories(${PROJECT_NAME} PRIVATE
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/source
    ${SIMPLELINK_CC13XX_CC26XX_SDK_INSTALL_DIR}/kernel/nortos
)

# # Libraries to link
# target_link_libraries(${PROJECT_NAME}
#     gcc
#     c
#     m
# )

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

