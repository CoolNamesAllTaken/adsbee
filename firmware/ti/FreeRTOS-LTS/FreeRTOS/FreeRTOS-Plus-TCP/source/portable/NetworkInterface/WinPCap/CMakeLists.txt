if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "WIN_PCAP") ) )
    return()
endif()

find_package(PCAP REQUIRED)

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    FaultInjection.c
    NetworkInterface.c
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
    ${PCAP_LIBRARY}
)

