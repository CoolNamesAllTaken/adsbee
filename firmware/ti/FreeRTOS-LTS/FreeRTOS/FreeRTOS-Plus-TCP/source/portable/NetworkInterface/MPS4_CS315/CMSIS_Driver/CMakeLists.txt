# Copyright 2023 Arm Limited and/or its affiliates
# <open-source-office@arm.com>
# SPDX-License-Identifier: MIT

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    ETH_LAN91C111.c
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    .
)
