if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "ATSAM4E") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    component/gmac.h
    instance/gmac.h
    ethernet_phy.c
    ethernet_phy.h
    gmac.c
    gmac.h
    NetworkInterface.c
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
