if (NOT (FREERTOS_PLUS_TCP_NETWORK_IF STREQUAL "POSIX") )
    return()
endif()

find_package(PCAP REQUIRED)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads)

#------------------------------------------------------------------------------
add_library( freertos_plus_tcp_network_if STATIC )

target_sources( freertos_plus_tcp_network_if
  PRIVATE
    NetworkInterface.c
)

target_compile_options( freertos_plus_tcp_network_if
  PRIVATE
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-declaration-after-statement>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-documentation>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
    $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-padded>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-shorten-64-to-32>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-undef>
    $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
    $<$<COMPILE_LANG_AND_ID:C,GNU>:-Wno-unused-parameter>
)

target_link_libraries( freertos_plus_tcp_network_if
  PUBLIC
    freertos_plus_tcp_port
    freertos_plus_tcp_network_if_common
  PRIVATE
    freertos_kernel
    freertos_plus_tcp
    ${PCAP_LIBRARY}
    Threads::Threads
)
