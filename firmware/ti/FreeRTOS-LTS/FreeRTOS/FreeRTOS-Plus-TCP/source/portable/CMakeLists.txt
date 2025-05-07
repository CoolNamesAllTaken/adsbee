add_library( freertos_plus_tcp_port STATIC )

target_sources( freertos_plus_tcp_port
  PRIVATE
    BufferManagement/BufferAllocation_${FREERTOS_PLUS_TCP_BUFFER_ALLOCATION}.c
    # Note: There's NetworkInterface/pic32mzef that has it's own BufferAllocation_2.c
)

target_include_directories( freertos_plus_tcp_port
  PUBLIC
    # Using Cmake to detect except for unknown compilers.
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_COMPILER},CCS>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/CCS>
    $<$<C_COMPILER_ID:CCS>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/CCS>
    $<$<C_COMPILER_ID:GNU,Clang,ARMClang>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/GCC>
    $<$<C_COMPILER_ID:Tasking>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/Tasking>
    $<$<C_COMPILER_ID:IAR>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/IAR>
    $<$<C_COMPILER_ID:ARMCC>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/Keil>
    $<$<C_COMPILER_ID:MSVC>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/MSVC>
    $<$<STREQUAL:${FREERTOS_PLUS_TCP_COMPILER},Renesas>:${CMAKE_CURRENT_SOURCE_DIR}/Compiler/Renesas>
)

target_compile_options( freertos_plus_tcp_port
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-extra-semi-stmt>
    $<$<COMPILE_LANG_AND_ID:C,GNU>:-Wno-pedantic> # Strange definition for STATIC_ASSERT
)

target_link_libraries( freertos_plus_tcp_port
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
    freertos_plus_tcp_network_if
)

#------------------------------------------------------------------------------
add_subdirectory(NetworkInterface)
