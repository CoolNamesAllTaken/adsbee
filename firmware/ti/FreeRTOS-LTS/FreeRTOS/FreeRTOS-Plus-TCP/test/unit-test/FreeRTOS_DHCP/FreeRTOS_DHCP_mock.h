#include "FreeRTOS_DHCP.h"

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress );
