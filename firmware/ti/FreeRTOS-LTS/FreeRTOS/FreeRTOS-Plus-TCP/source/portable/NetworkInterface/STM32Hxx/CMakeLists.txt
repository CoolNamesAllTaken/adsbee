if (NOT ( (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "STM32HXX") ) )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
    stm32h7xx_hal_eth.h
    stm32hxx_hal_eth.c
    stm32hxx_hal_eth.h
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
