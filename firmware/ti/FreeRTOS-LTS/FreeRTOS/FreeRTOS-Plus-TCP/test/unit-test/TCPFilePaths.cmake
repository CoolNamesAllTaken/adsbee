# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.

# TCP library source files.
set( TCP_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_ARP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_BitConfig.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DHCP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DHCPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DNS.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DNS_Cache.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DNS_Callback.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DNS_Networking.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_DNS_Parser.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_ICMP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IP_Timers.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IP_Utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv4_Sockets.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv4_Utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv6_Sockets.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_IPv6_Utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_ND.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_RA.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_Routing.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_Sockets.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_Stream_Buffer.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_IP_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_IP_IPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Reception.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_State_Handling.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_State_Handling_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_State_Handling_IPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Transmission.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Transmission_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Transmission_IPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Utils.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Utils_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_Utils_IPv6.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_TCP_WIN.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_Tiny_TCP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_UDP_IP.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_UDP_IPv4.c"
     "${CMAKE_CURRENT_LIST_DIR}/../../source/FreeRTOS_UDP_IPv6.c" )

# TCP library Include directories.
set( TCP_INCLUDE_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/../../source/include
     ${CMAKE_CURRENT_LIST_DIR}/../../source/portable/Buffermanagement
     ${CMAKE_CURRENT_LIST_DIR}/../../source/portable/Compiler/MSVC
     ${CMAKE_CURRENT_LIST_DIR}/stubs )

# Kernel source files.
set( KERNEL_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/croutine.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/event_groups.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/list.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/queue.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/stream_buffer.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/tasks.c"
     "${CMAKE_CURRENT_LIST_DIR}/../FreeRTOS-Kernel/timers.c" )
