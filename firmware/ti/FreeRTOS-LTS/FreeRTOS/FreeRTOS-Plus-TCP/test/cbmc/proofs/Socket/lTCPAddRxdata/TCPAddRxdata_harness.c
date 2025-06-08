/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"

/* CBMC includes. */
#include "memory_assignments.c"

/****************************************************************
* Signature of function under test
****************************************************************/

StreamBuffer_t * __CPROVER_file_local_FreeRTOS_Sockets_c_prvTCPCreateStream( FreeRTOS_Socket_t * pxSocket,
                                                                             BaseType_t xIsInputStream );


void __CPROVER_file_local_FreeRTOS_Sockets_c_vTCPAddRxdata_Callback( FreeRTOS_Socket_t * pxSocket,
                                                                     const uint8_t * pcData,
                                                                     uint32_t ulByteCount );

void __CPROVER_file_local_FreeRTOS_Sockets_c_vTCPAddRxdata_Stored( FreeRTOS_Socket_t * pxSocket );

/* Abstraction of this functions allocate and return xWantedSize data. */
void * pvPortMallocLarge( size_t xWantedSize )
{
    return safeMalloc( xWantedSize );
}

void harness()
{
    FreeRTOS_Socket_t * pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
    size_t uxOffset;
    const uint8_t * pcData;
    uint32_t ulByteCount;

    /* This function expect socket to be not NULL, as it has been validated previously */
    __CPROVER_assume( pxSocket != NULL );

    /* Assume size of streams to be in the range of maximum supported size.*/
    __CPROVER_assume( pxSocket->u.xTCP.uxRxStreamSize >= 0 && pxSocket->u.xTCP.uxRxStreamSize < ipconfigTCP_RX_BUFFER_LENGTH );
    __CPROVER_assume( pxSocket->u.xTCP.uxTxStreamSize >= 0 && pxSocket->u.xTCP.uxTxStreamSize < ipconfigTCP_TX_BUFFER_LENGTH );

    pcData = safeMalloc( ulByteCount );

    lTCPAddRxdata( pxSocket, uxOffset, pcData, ulByteCount );
}
