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

int32_t __CPROVER_file_local_FreeRTOS_Sockets_c_prvRecvFrom_CopyPacket( uint8_t * pucEthernetBuffer,
                                                                        void * pvBuffer,
                                                                        size_t uxBufferLength,
                                                                        BaseType_t xFlags,
                                                                        int32_t lDataLength );

void harness()
{
    uint8_t * pucEthernetBuffer;
    uint8_t * pvBuffer;
    size_t uxBufferLength;
    BaseType_t xFlags;
    int32_t lDataLength;

    __CPROVER_assume( lDataLength > 0 && lDataLength < ipconfigNETWORK_MTU );
    pucEthernetBuffer = safeMalloc( lDataLength );
    __CPROVER_assume( pucEthernetBuffer != NULL );

    __CPROVER_assume( uxBufferLength > 0 && uxBufferLength < ipconfigNETWORK_MTU );

    if( nondet_bool() )
    {
        /* This is to validate case when zero copy flag is not set*/
        __CPROVER_assume( xFlags == 0U );

        /* When zero flag is not set, need to provide a buffer in which received data will be copied. */
        pvBuffer = safeMalloc( uxBufferLength );
        __CPROVER_assume( pvBuffer != NULL );
        __CPROVER_file_local_FreeRTOS_Sockets_c_prvRecvFrom_CopyPacket( pucEthernetBuffer, pvBuffer, uxBufferLength, xFlags, lDataLength );
    }
    else
    {
        __CPROVER_assume( pvBuffer == NULL );

        /* The zero copy flag was set.  pvBuffer is not a buffer into which
         * the received data can be copied, but a pointer that must be set to
         * point to the buffer in which the received data has already been
         * placed. */
        __CPROVER_assume( xFlags == FREERTOS_ZERO_COPY );
        __CPROVER_file_local_FreeRTOS_Sockets_c_prvRecvFrom_CopyPacket( pucEthernetBuffer, &pvBuffer, uxBufferLength, xFlags, lDataLength );

        /* Postconditions */
        __CPROVER_assert( pvBuffer != NULL, "pvBuffer can not be NULL" );
    }
}
