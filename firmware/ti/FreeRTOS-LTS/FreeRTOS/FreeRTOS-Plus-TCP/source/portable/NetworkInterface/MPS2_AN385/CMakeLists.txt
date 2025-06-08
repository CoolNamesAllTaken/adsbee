if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "MPS2_AN385") )
    return()
endif()

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    ether_lan9118/SMM_MPS2.h
    ether_lan9118/smsc9220_emac_config.h
    ether_lan9118/smsc9220_eth_drv.c
    ether_lan9118/smsc9220_eth_drv.h
    NetworkInterface.c
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    ether_lan9118
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
