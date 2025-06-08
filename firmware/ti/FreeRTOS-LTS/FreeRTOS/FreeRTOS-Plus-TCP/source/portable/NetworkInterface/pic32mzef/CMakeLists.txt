if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "PIC32MZEF_ETH") OR
          (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "PIC32MZEF_WIFI") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

# What about BufferAllocation_2.c here?
target_sources( freertos_plus_tcp_network_if
  PRIVATE
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_NETWORK_IF},PIC32MZEF_ETH>:NetworkInterface_eth.c>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_NETWORK_IF},PIC32MZEF_WIFI>:NetworkInterface_wifi.c>
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
