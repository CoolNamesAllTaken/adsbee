
cmake_minimum_required(VERSION 3.15)
cmake_policy(SET CMP0048 NEW) # project version
cmake_policy(SET CMP0076 NEW) # full paths

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/cmake_modules")

########################################################################
# Project Details
project(FreeRTOS-Plus-TCP
        VERSION 3.1.0
        DESCRIPTION "FreeRTOS TCP/UDP Network Layer"
        HOMEPAGE_URL https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/index.html
        LANGUAGES C)

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Options
option(FREERTOS_PLUS_TCP_BUILD_TEST "Build the test for FreeRTOS Plus TCP" OFF)
option(FREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS "Enable the build checks for FreeRTOS-Plus-TCP" OFF)

# Configuration
# Override these at project level with:
#   Optional: set(FREERTOS_PLUS_TCP_BUFFER_ALLOCATION "1" CACHE STRING "" FORCE)
#   Optional: set(FREERTOS_PLUS_TCP_COMPILER "" CACHE STRING "" FORCE)
#   Required: set(FREERTOS_PLUS_TCP_NETWORK_IF "POSIX" CACHE STRING "" FORCE)

# Select the appropriate buffer allocation method.
# See: https://freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html
if (NOT FREERTOS_PLUS_TCP_BUFFER_ALLOCATION)
    message(STATUS "Using default FREERTOS_PLUS_TCP_BUFFER_ALLOCATION = 2")
    set(FREERTOS_PLUS_TCP_BUFFER_ALLOCATION "2" CACHE STRING "FreeRTOS buffer allocation model number. 1 .. 2.")
endif()

# Select the Compiler - if left blank will detect using CMake
# Note relies on CMake to detect over any setting here.
# Valid options are:
#   FREERTOS_PLUS_TCP_COMPILER | Detected | CMake
#   -------------------------------------------------
#   CCS                        | No       | ?TBD?
#   GCC                        | Yes      | GNU
#   IAR                        | Yes      | IAR
#   Keil                       | Yes      | ARMCC
#   MSVC                       | Yes      | MSVC # Note only for MinGW
#   Renesas                    | No       | ?TBD?
# Will always a attempt to detect and if detectable double checks that the compiler is set correctly.
set(FREERTOS_PLUS_TCP_COMPILER "" CACHE STRING "FreeRTOS Plus TCP Compiler Selection")


# Select the appropriate network interface
# This will fail the CMake preparation step if not set to one of those values.
set(FREERTOS_PLUS_TCP_NETWORK_IF "" CACHE STRING "FreeRTOS Plus TCP Network Interface selection")
set(FREERTOS_PLUS_TCP_NETWORK_IF_LIST
    A_CUSTOM_NETWORK_IF
    ATSAM43 ATSAME5x # AT
    DRIVER_SAM
    ESP32
    KSZ8851SNL
    LIBSLIRP
    LOOPBACK
    LPC17xx LPC18xx LPC54018
    M487
    MPS2_AN385
    MPS3_AN552
    MW300_RD
    NXP1060
    PIC32MZEF_ETH PIC32MZEF_WIFI
    POSIX WIN_PCAP  # Native Linux & Windows respectively
    RX
    SH2A
    STM32FXX STM32HXX # ST Micro
    MSP432
    TM4C
    XILINX_ULTRASCALE ZYNQ # AMD/Xilinx
)

if(NOT FREERTOS_PLUS_TCP_NETWORK_IF)
    # Attempt to detect the system.
    if(UNIX)
        message(STATUS "Detected UNIX/Posix system setting FREERTOS_PLUS_TCP_NETWORK_IF = POSIX")
        set(FREERTOS_PLUS_TCP_NETWORK_IF POSIX)
    elseif(MINGW)
        message(STATUS "Detected Windows MinGW system setting FREERTOS_PLUS_TCP_NETWORK_IF = WIN_PCAP")
        set(FREERTOS_PLUS_TCP_NETWORK_IF WIN_PCAP)
    endif()
endif()

if(NOT FREERTOS_PLUS_TCP_NETWORK_IF IN_LIST FREERTOS_PLUS_TCP_NETWORK_IF_LIST )
    message(FATAL_ERROR " FREERTOS_PLUS_TCP_NETWORK_IF is '${FREERTOS_PLUS_TCP_NETWORK_IF}'.\n"
        " Please specify it from top-level CMake file (example):\n"
        "   set(FREERTOS_PLUS_TCP_NETWORK_IF POSIX CACHE STRING \"\")\n"
        " or from CMake command line option:\n"
        "   -DFREERTOS_PLUS_TCP_NETWORK_IF=POSIX\n"
        " \n"
        " Available port options: (Tested means compiled with that variant)\n"
        " A_CUSTOM_NETWORK_IF    Target: User Defined\n"
        " ATSAM4E                Target: ATSAM4E            Tested: TODO\n"
        " ATSAME5x               Target: ATSAME5x           Tested: TODO\n"
        " DRIVER_SAM             Target: Driver SAM         Tested: TODO\n"
        " ESP32                  Target: ESP-32             Tested: TODO\n"
        " KSZ8851SNL             Target: ksz8851snl         Tested: TODO\n"
        " LIBSLIRP               Target: libslirp           Tested: TODO\n"
        " POSIX                  Target: linux/Posix\n"
        " LOOPBACK               Target: loopback           Tested: TODO\n"
        " LPC17xx                Target: LPC17xx            Tested: TODO\n"
        " LPC18xx                Target: LPC18xx            Tested: TODO\n"
        " LPC54018               Target: LPC54018           Tested: TODO\n"
        " M487                   Target: M487               Tested: TODO\n"
        " MPS2_AN385             Target: MPS2_AN385         Tested: TODO\n"
        " MPS3_AN552             Target: MPS3_AN552"
        " MW300_RD               Target: mw300_rd           Tested: TODO\n"
        " NXP1060                Target: NXP1060            Tested: TODO\n"
        " PIC32MZEF_ETH          Target: pic32mzef ethernet Tested: TODO\n"
        " PIC32MZEF_WIFI         Target: pic32mzef Wifi     Tested: TODO\n"
        " RX                     Target: RX                 Tested: TODO\n"
        " SH2A                   Target: SH2A               Tested: TODO\n"
        " STM32FXX               Target: STM32Fxx           Tested: TODO\n"
        " STM32HXX               Target: STM32Hxx           Tested: TODO\n"
        " MSP432                 Target: MSP432             Tested: TODO\n"
        " TM4C                   Target: TM4C               Tested: TODO\n"
        " WIN_PCAP               Target: Windows            Tested: TODO\n"
        " XILINX_ULTRASCALE      Target: Xilinx Ultrascale  Tested: TODO\n"
        " ZYNQ                   Target: Xilinx Zynq")
elseif((FREERTOS_PORT STREQUAL "A_CUSTOM_PORT") AND (NOT TARGET freertos_kernel_port) )
    message(FATAL_ERROR " FREERTOS_PLUS_TCP_NETWORK_IF is set to A_CUSTOM_NETWORK_IF.\n"
    " Please specify the custom network interface target with all necessary files.\n"
    " For example, assuming a directory of:\n"
    "  FreeRTOSCustomNetworkInterface/\n"
    "    CMakeLists.txt\n"
    "    NetworkInterface.c\n\n"
    " Where FreeRTOSCustomNetworkInterface/CMakeLists.txt is a modified version of:\n"
    "   add_library(freertos_plus_tcp_network_if STATIC)\n\n"
    "   target_sources(freertos_plus_tcp_network_if\n"
    "     PRIVATE\n"
    "       NetworkInterface.c)\n\n"
    "   target_include_directories(freertos_plus_tcp_network_if\n"
    "     PUBLIC\n"
    "      .)\n\n"
    "   target_link_libraries(freertos_plus_tcp_network_if\n"
    "     PUBLIC\n"
    "       freertos_plus_tcp_port\n"
    "       freertos_plus_tcp_network_if_common\n"
    "     PRIVATE\n"
    "       freertos_kernel)")
endif()

# There is also the need to add a target - typically an interface library that describes the
# Configuration for FreeRTOS-Kernel and FreeRTOS-Plus-TCP.
# This is called freertos_config

########################################################################
# External Dependencies
# Note: For backwards compatibility - still have .gitmodules defining submodules
# To support fetching content in a higher level project see
#   README.md `Consume with CMake`
# This will allow you to upgrade submodules and have one common submodule for
# all your builds despite multiple submodules having different versions.
include(FetchContent)

FetchContent_Declare( freertos_kernel
  GIT_REPOSITORY https://github.com/FreeRTOS/FreeRTOS-Kernel.git
  GIT_TAG        main
)

FetchContent_Declare( cmock
  GIT_REPOSITORY https://github.com/ThrowTheSwitch/CMock
  GIT_TAG        v2.5.3
)

add_subdirectory(source)
add_subdirectory(tools)
add_subdirectory(test)

FetchContent_MakeAvailable(freertos_kernel cmock)
