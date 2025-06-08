/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

#include "FreeRTOS_IP.h"

volatile BaseType_t xInsideInterrupt = pdFALSE;

/* Provide a main function for the build to succeed. */
int main()
{
    return 0;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes )
{
    ( void ) xRequestedSizeBytes;

    return NULL;
}
/*-----------------------------------------------------------*/

BaseType_t vNetworkBufferReleaseFromISR( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    ( void ) pxNetworkBuffer;

    return pdPASS;
}
/*-----------------------------------------------------------*/

BaseType_t xApplicationGetRandomNumber( uint32_t * pulNumber )
{
    ( void ) pulNumber;

    return 0;
}
/*-----------------------------------------------------------*/

size_t xPortGetMinimumEverFreeHeapSize( void )
{
    return 0;
}
/*-----------------------------------------------------------*/

const char * pcApplicationHostnameHook( void )
{
    return NULL;
}
/*-----------------------------------------------------------*/

uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
                                             uint16_t usSourcePort,
                                             uint32_t ulDestinationAddress,
                                             uint16_t usDestinationPort )
{
    ( void ) ulSourceAddress;
    ( void ) usSourcePort;
    ( void ) ulDestinationAddress;
    ( void ) usDestinationPort;

    return 0;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
    return pdPASS;
}
/*-----------------------------------------------------------*/

void vApplicationIPNetworkEventHook_Multi( eIPCallbackEvent_t eNetworkEvent,
                                           struct xNetworkEndPoint * pxEndPoint )
{
    ( void ) eNetworkEvent;
    ( void ) pxEndPoint;
}
/*-----------------------------------------------------------*/

void vApplicationDaemonTaskStartupHook( void )
{
}
/*-----------------------------------------------------------*/

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    ( void ) ppxTimerTaskTCBBuffer;
    ( void ) ppxTimerTaskStackBuffer;
    ( void ) pulTimerTaskStackSize;
}
/*-----------------------------------------------------------*/

void vPortDeleteThread( void * pvTaskToDelete )
{
    ( void ) pvTaskToDelete;
}

void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
}

uint32_t ulGetRunTimeCounterValue( void )
{
    return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
    return pdPASS;
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
}
/*-----------------------------------------------------------*/

void * pvPortMalloc( size_t xWantedSize )
{
    return malloc( xWantedSize );
}
/*-----------------------------------------------------------*/

void vPortFree( void * pv )
{
    free( pv );
}
/*-----------------------------------------------------------*/

StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    ( void ) pxTopOfStack;
    ( void ) pxCode;
    ( void ) pvParameters;

    return NULL;
}
/*-----------------------------------------------------------*/

void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber )
{
    ( void ) ulInterruptNumber;
}
/*-----------------------------------------------------------*/

void vPortCloseRunningThread( void * pvTaskToDelete,
                              volatile BaseType_t * pxPendYield )
{
    ( void ) pvTaskToDelete;
    ( void ) pxPendYield;
}
/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    ( void ) ppxIdleTaskTCBBuffer;
    ( void ) ppxIdleTaskStackBuffer;
    ( void ) pulIdleTaskStackSize;
}
/*-----------------------------------------------------------*/

void vConfigureTimerForRunTimeStats( void )
{
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t bReleaseAfterSend )
{
    ( void ) pxNetworkBuffer;
    ( void ) bReleaseAfterSend;

    return pdFAIL;
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_SendPingRequest( uint32_t ulIPAddress,
                                     size_t uxNumberOfBytesToSend,
                                     TickType_t uxBlockTimeTicks )
{
    ( void ) ulIPAddress;
    ( void ) uxNumberOfBytesToSend;
    ( void ) uxBlockTimeTicks;

    return pdFAIL;
}
/*-----------------------------------------------------------*/

eDHCPCallbackAnswer_t xApplicationDHCPHook_Multi( eDHCPCallbackPhase_t eDHCPPhase,
                                                  struct xNetworkEndPoint * pxEndPoint,
                                                  IP_Address_t * pxIPAddress )
{
    /* Provide a stub for this function. */
    return eDHCPContinue;
}
/*-----------------------------------------------------------*/
