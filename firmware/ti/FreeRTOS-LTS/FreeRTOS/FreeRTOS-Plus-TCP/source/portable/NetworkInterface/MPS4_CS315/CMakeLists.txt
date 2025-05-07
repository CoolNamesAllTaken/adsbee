# Copyright 2024 Arm Limited and/or its affiliates
# <open-source-office@arm.com>
# SPDX-License-Identifier: MIT

if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "MPS4_CS315") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

# CMSIS Ethernet driver for LAN91C111
add_subdirectory(CMSIS_Driver)

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    Device/Include
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
