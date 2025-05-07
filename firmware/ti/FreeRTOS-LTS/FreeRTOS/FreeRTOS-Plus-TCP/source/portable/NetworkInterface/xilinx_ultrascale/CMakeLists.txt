if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "XILINX_ULTRASCALE") )
    return()
endif()

if(NOT TARGET xil_bsp)
    message(FATAL_ERROR "For FREERTOS_PLUS_TCP_NETWORK_IF=XILINX_ULTRASCALE must have a target for the xil_bsp")
endif()

# XILINX_ULTRASCALE port shares uncached_memory.c and .h with FreeRTOS-Plus-FAT.
# Separating out so it can potentially be included there as well.
#------------------------------------------------------------------------------
add_library(freertos_xil_uncached_memory STATIC)

target_sources(freertos_xil_uncached_memory
  PRIVATE
    uncached_memory.c
    uncached_memory.h
)

target_include_directories(freertos_xil_uncached_memory
  PUBLIC
    .
  PRIVATE
    ..
)

target_link_libraries(freertos_xil_uncached_memory
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
    freertos_plus_tcp_network_if
    xil_bsp
)

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
    x_emacpsif_dma.c
    x_emacpsif_hw.c
    x_emacpsif_hw.h
    x_emacpsif_physpeed.c
    x_emacpsif.h
    x_topology.h
)

target_include_directories( freertos_plus_tcp_network_if
  PRIVATE
    ..
)

target_compile_options( freertos_plus_tcp_network_if
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-declaration-after-statement>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-padded>
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
    freertos_xil_uncached_memory
    xil_bsp
)
