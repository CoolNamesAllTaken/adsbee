add_library( freertos_plus_tcp_network_if_common STATIC )

target_sources( freertos_plus_tcp_network_if_common
  PRIVATE
    Common/phyHandling.c
    include/phyHandling.h
)

target_include_directories( freertos_plus_tcp_network_if_common
  PUBLIC
    include
)

target_compile_options( freertos_plus_tcp_network_if_common
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-conditional-uninitialized>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-implicit-int-conversion>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-uninitialized>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-but-set-variable>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
)

target_link_libraries( freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
)

#------------------------------------------------------------------------------
add_subdirectory(ATSAM4E)
add_subdirectory(ATSAME5x)
#add_subdirectory(board_family) - This is only an example.
add_subdirectory(DriverSAM)
add_subdirectory(esp32)
add_subdirectory(ksz8851snl)
add_subdirectory(libslirp)
add_subdirectory(linux)
add_subdirectory(loopback)
add_subdirectory(LPC17xx)
add_subdirectory(LPC18xx)
add_subdirectory(LPC54018)
add_subdirectory(M487)
add_subdirectory(MPS2_AN385)
add_subdirectory(MPS3_AN552)
add_subdirectory(MPS4_CS315)
add_subdirectory(NXP1060)
add_subdirectory(mw300_rd)
add_subdirectory(pic32mzef)
add_subdirectory(RX)
add_subdirectory(SH2A)
add_subdirectory(STM32Fxx)
add_subdirectory(STM32Hxx)
add_subdirectory(ThirdParty/MSP432)
add_subdirectory(TM4C)
add_subdirectory(WinPCap)
add_subdirectory(xilinx_ultrascale)
add_subdirectory(Zynq)
