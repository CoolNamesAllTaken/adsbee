if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "LPC54018") )
    return()
endif()

if(NOT TARGET fsl_enet_driver)
    message(FATAL_ERROR "For FREERTOS_PLUS_TCP_NETWORK_IF=LPC54018 must have a target for the fsl_enet_driver")
endif()
#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

target_link_libraries(freertos_plus_tcp_network_if
  PRIVATE
    lpc54018_driver
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
