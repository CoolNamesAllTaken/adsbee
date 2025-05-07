/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"

void harness()
{
    NetworkEndPoint_t * pxEndPoint_Test = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );

    /*
     * Here the assumption that pxEndPoint_Test != NULL [__CPROVER_assume( pxEndPoint_Test != NULL );]
     * is not made as pxEndPoint_Test == NULL is a valid use case.
     */

    FreeRTOS_ClearARP( pxEndPoint_Test );
}
