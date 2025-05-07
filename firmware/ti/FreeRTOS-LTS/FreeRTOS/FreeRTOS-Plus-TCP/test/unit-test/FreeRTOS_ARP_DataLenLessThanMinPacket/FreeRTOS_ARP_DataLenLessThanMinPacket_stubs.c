/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

struct xNetworkEndPoint * pxNetworkEndPoints = NULL;

NetworkBufferDescriptor_t * pxARPWaitingNetworkBuffer = NULL;

volatile BaseType_t xInsideInterrupt = pdFALSE;

/** @brief For convenience, a MAC address of all 0xffs is defined const for quick
 * reference. */
const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/** @brief Structure that stores the netmask, gateway address and DNS server addresses. */
NetworkAddressingParameters_t xNetworkAddressing =
{
    0xC0C0C0C0, /* 192.192.192.192 - Default IP address. */
    0xFFFFFF00, /* 255.255.255.0 - Netmask. */
    0xC0C0C001, /* 192.192.192.1 - Gateway Address. */
    0x01020304, /* 1.2.3.4 - DNS server address. */
    0xC0C0C0FF
};              /* 192.192.192.255 - Broadcast address. */

size_t xPortGetMinimumEverFreeHeapSize( void )
{
    return 0;
}


/* Even though the function is defined in main.c, the rule is violated. */
/* misra_c_2012_rule_8_6_violation */
extern BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                                  const char * pcName )
{
}

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     StackType_t * pxEndOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
}

const char * pcApplicationHostnameHook( void )
{
}
uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                             uint16_t usSourcePort,
                                             uint32_t ulDestinationAddress,
                                             uint16_t usDestinationPort )
{
}
/* This function shall be defined by the application. */
void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                           struct xNetworkEndPoint * pxEndPoint )
{
}
BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
}
void vApplicationDaemonTaskStartupHook( void )
{
}
void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     configSTACK_DEPTH_TYPE * puxTimerTaskStackSize )
{
}
void vPortDeleteThread( void * pvTaskToDelete )
{
}
void vApplicationIdleHook( void )
{
}
void vApplicationTickHook( void )
{
}
unsigned long ulGetRunTimeCounterValue( void )
{
}
void vPortEndScheduler( void )
{
}
BaseType_t xPortStartScheduler( void )
{
}
void vPortEnterCritical( void )
{
}
void vPortExitCritical( void )
{
}

void * pvPortMalloc( size_t xWantedSize )
{
    return malloc( xWantedSize );
}

void vPortFree( void * pv )
{
    free( pv );
}

void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber )
{
}
void vPortCloseRunningThread( void * pvTaskToDelete,
                              volatile BaseType_t * pxPendYield )
{
}
void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    configSTACK_DEPTH_TYPE * puxIdleTaskStackSize )
{
}
void vConfigureTimerForRunTimeStats( void )
{
}

/**
 * @brief Send an ND advertisement.
 * @param[in] pxEndPoint: The end-point for which an ND advertisement should be sent.
 */
void FreeRTOS_OutputAdvertiseIPv6( NetworkEndPoint_t * pxEndPoint )
{
}
