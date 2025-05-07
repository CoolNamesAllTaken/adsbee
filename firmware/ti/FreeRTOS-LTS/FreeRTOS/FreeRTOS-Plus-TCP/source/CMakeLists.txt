add_library( freertos_plus_tcp STATIC )

target_sources( freertos_plus_tcp
  PRIVATE
      include/FreeRTOS_ARP.h
      include/FreeRTOS_BitConfig.h
      include/FreeRTOS_DHCP.h
      include/FreeRTOS_DHCPv6.h
      include/FreeRTOS_DNS.h
      include/FreeRTOS_DNS_Cache.h
      include/FreeRTOS_DNS_Callback.h
      include/FreeRTOS_DNS_Globals.h
      include/FreeRTOS_DNS_Networking.h
      include/FreeRTOS_DNS_Parser.h
      include/FreeRTOS_ICMP.h
      include/FreeRTOS_IP.h
      include/FreeRTOS_IP_Common.h
      include/FreeRTOS_IP_Private.h
      include/FreeRTOS_IP_Timers.h
      include/FreeRTOS_IP_Utils.h
      include/FreeRTOS_IPv4.h
      include/FreeRTOS_IPv4_Private.h
      include/FreeRTOS_IPv4_Sockets.h
      include/FreeRTOS_IPv4_Utils.h
      include/FreeRTOS_IPv6.h
      include/FreeRTOS_IPv6_Private.h
      include/FreeRTOS_IPv6_Sockets.h
      include/FreeRTOS_IPv6_Utils.h
      include/FreeRTOS_ND.h
      include/FreeRTOS_Routing.h
      include/FreeRTOS_Sockets.h
      include/FreeRTOS_Stream_Buffer.h
      include/FreeRTOS_TCP_IP.h
      include/FreeRTOS_TCP_Reception.h
      include/FreeRTOS_TCP_State_Handling.h
      include/FreeRTOS_TCP_Transmission.h
      include/FreeRTOS_TCP_Utils.h
      include/FreeRTOS_TCP_WIN.h
      include/FreeRTOS_UDP_IP.h
      include/FreeRTOSIPConfigDefaults.h
      include/FreeRTOSIPDeprecatedDefinitions.h
      include/IPTraceMacroDefaults.h
      include/NetworkBufferManagement.h
      include/NetworkInterface.h

      FreeRTOS_ARP.c
      FreeRTOS_BitConfig.c
      FreeRTOS_DHCP.c
      FreeRTOS_DHCPv6.c
      FreeRTOS_DNS.c
      FreeRTOS_DNS_Cache.c
      FreeRTOS_DNS_Callback.c
      FreeRTOS_DNS_Networking.c
      FreeRTOS_DNS_Parser.c
      FreeRTOS_ICMP.c
      FreeRTOS_IP.c
      FreeRTOS_IP_Timers.c
      FreeRTOS_IP_Utils.c
      FreeRTOS_IPv4.c
      FreeRTOS_IPv4_Sockets.c
      FreeRTOS_IPv4_Utils.c
      FreeRTOS_IPv6.c
      FreeRTOS_IPv6_Sockets.c
      FreeRTOS_IPv6_Utils.c
      FreeRTOS_ND.c
      FreeRTOS_RA.c
      FreeRTOS_Routing.c
      FreeRTOS_Sockets.c
      FreeRTOS_Stream_Buffer.c
      FreeRTOS_TCP_IP.c
      FreeRTOS_TCP_IP_IPv4.c
      FreeRTOS_TCP_IP_IPv6.c
      FreeRTOS_TCP_Reception.c
      FreeRTOS_TCP_State_Handling.c
      FreeRTOS_TCP_State_Handling_IPv4.c
      FreeRTOS_TCP_State_Handling_IPv6.c
      FreeRTOS_TCP_Transmission.c
      FreeRTOS_TCP_Transmission_IPv4.c
      FreeRTOS_TCP_Transmission_IPv6.c
      FreeRTOS_TCP_Utils.c
      FreeRTOS_TCP_Utils_IPv4.c
      FreeRTOS_TCP_Utils_IPv6.c
      FreeRTOS_TCP_WIN.c
      FreeRTOS_Tiny_TCP.c
      FreeRTOS_UDP_IP.c
      FreeRTOS_UDP_IPv4.c
      FreeRTOS_UDP_IPv6.c
)

target_include_directories( freertos_plus_tcp
  PUBLIC
    include
)

target_link_libraries( freertos_plus_tcp
  PUBLIC
    freertos_config
    freertos_plus_tcp_port # for pack_struct_start.h
  PRIVATE
    freertos_kernel
    freertos_plus_tcp_network_if
    freertos_plus_tcp_utilities
)

add_subdirectory(portable)
