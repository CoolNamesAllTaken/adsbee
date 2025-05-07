tcp_netstat.c : it introduces the following function:

    `BaseType_t vGetMetrics( MetricsType_t * pxMetrics )`

It collects information: all port numbers in use, all UDP sockets, all TCP sockets and their connections.

Make sure that your FreeRTOSIPConfig.h includes tools/tcp_utilities/include/tcp_netstat.h:

    `@include "tcp_netstat.h"`

because it will define 2 important macro's:

    #define iptraceNETWORK_INTERFACE_INPUT( uxDataLength, pucEthernetBuffer )

    #define iptraceNETWORK_INTERFACE_OUTPUT( uxDataLength, pucEthernetBuffer )

These macro's will be called when an Ethernet packet has been received or sent.

When collecting socket and port information, it will iterate through the list of sockets, filling arrays of structures.
