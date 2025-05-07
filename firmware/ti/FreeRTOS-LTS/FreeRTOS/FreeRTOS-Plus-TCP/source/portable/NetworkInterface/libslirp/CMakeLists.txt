if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "LIBSLIRP") )
    return()
endif()

if(NOT TARGET slirp)
    message(FATAL_ERROR "For FREERTOS_PLUS_TCP_NETWORK_IF=LIBSLIRP must have a target for the slirp")
endif()
#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    MBuffNetifBackendLibslirp.c
    MBuffNetworkInterface.c
)

target_link_libraries(freertos_plus_tcp_network_if
  PRIVATE
    slirp
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)
