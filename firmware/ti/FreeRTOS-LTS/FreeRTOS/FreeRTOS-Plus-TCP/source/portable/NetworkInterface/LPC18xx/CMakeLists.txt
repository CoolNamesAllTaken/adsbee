if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "LPC18xx") )
    return()
endif()

if(NOT TARGET lpc17xx_driver)
    message(FATAL_ERROR "For FREERTOS_PLUS_TCP_NETWORK_IF=LPC18xx must have a target for the lpc18xx_driver")
endif()
#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

target_link_libraries(freertos_plus_tcp_network_if
  PRIVATE
    lpc18xx_driver
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
