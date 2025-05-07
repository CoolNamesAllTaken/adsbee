if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "DRIVER_SAM") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    gmac_SAM.c
    gmac_SAM.h
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
