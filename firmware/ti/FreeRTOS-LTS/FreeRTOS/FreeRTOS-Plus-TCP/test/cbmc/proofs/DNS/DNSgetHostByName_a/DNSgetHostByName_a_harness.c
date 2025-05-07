/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "cbmc.h"

/****************************************************************
* We abstract:
*
*   All kernel task scheduling functions since we are doing
*   sequential verification and the sequential verification of these
*   sequential primitives is done elsewhere.
*
*   Many methods in the FreeRTOS TCP API in stubs/freertos_api.c
*
*   DNS_ParseDNSReply proved memory safe elsewhere
*
*   prvCreateDNSMessage
*
* This proof assumes the length of pcHostName is bounded by
* MAX_HOSTNAME_LEN.  We have to bound this length because we have to
* bound the iterations of strcmp.
****************************************************************/

/****************************************************************
* Abstract DNS_ParseDNSReply proved memory safe in ParseDNSReply.
*
* We stub out his function to fill the payload buffer with
* unconstrained data and return an unconstrained size.
*
* The function under test uses only the return value of this
* function.
****************************************************************/

uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t uxBufferLength,
                            struct freertos_addrinfo ** ppxAddressInfo,
                            BaseType_t xExpected,
                            uint16_t usPort )
{
    __CPROVER_assert( pucUDPPayloadBuffer != NULL,
                      "Precondition: pucUDPPayloadBuffer != NULL" );

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return nondet_uint32();
}

/****************************************************************
* Abstract prvCreateDNSMessage
*
* This function writes a header, a hostname, and a constant amount of
* data into the payload buffer, and returns the amount of data
* written.  This abstraction just fills the entire buffer with
* unconstrained data and returns and unconstrained length.
****************************************************************/

size_t __CPROVER_file_local_FreeRTOS_DNS_c_prvCreateDNSMessage( uint8_t * pucUDPPayloadBuffer,
                                                                const char * pcHostName,
                                                                TickType_t uxIdentifier,
                                                                UBaseType_t uxHostType )
{
    __CPROVER_assert( pucUDPPayloadBuffer != NULL,
                      "Precondition: pucUDPPayloadBuffer != NULL" );
    __CPROVER_assert( pcHostName != NULL,
                      "Precondition: pcHostName != NULL" );

    __CPROVER_havoc_object( pucUDPPayloadBuffer );
    return nondet_sizet();
}

/****************************************************************
* A stub for a function callback.
****************************************************************/

void func( const char * pcHostName,
           void * pvSearchID,
           struct freertos_addrinfo * pxAddressInfo )
{
    __CPROVER_assert( pcHostName != NULL,
                      "Precondition: pcHostName != NULL" );
    __CPROVER_assert( pvSearchID != NULL,
                      "Precondition: pvSearchID != NULL" );

    /* pxAddressInfo is not validated for not being NULL as
     * pxAddressInfo could be NULL if there is a timeout or other errors. */
}

BaseType_t NetworkInterfaceOutputFunction_Stub( struct xNetworkInterface * pxDescriptor,
                                                NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxDescriptor != NULL, "The network interface cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer descriptor cannot be NULL." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "The ethernet buffer cannot be NULL." );
    BaseType_t ret;
    return ret;
}

/*We assume that the pxGetNetworkBufferWithDescriptor function is implemented correctly and returns a valid data structure. */
/*This is the mock to mimic the correct expected behavior. If this allocation fails, this might invalidate the proof. */
NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = ( NetworkBufferDescriptor_t * ) malloc( sizeof( NetworkBufferDescriptor_t ) );

    if( pxNetworkBuffer != NULL )
    {
        pxNetworkBuffer->pucEthernetBuffer = malloc( xRequestedSizeBytes + ipUDP_PAYLOAD_IP_TYPE_OFFSET );

        if( pxNetworkBuffer->pucEthernetBuffer == NULL )
        {
            free( pxNetworkBuffer );
            pxNetworkBuffer = NULL;
        }
        else
        {
            pxNetworkBuffer->pucEthernetBuffer = ( ( uint8_t * ) pxNetworkBuffer->pucEthernetBuffer ) + ipUDP_PAYLOAD_IP_TYPE_OFFSET;
            pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
        }
    }

    return pxNetworkBuffer;
}

Socket_t DNS_CreateSocket( TickType_t uxReadTimeout_ticks )
{
    Socket_t xSock = safeMalloc( sizeof( struct xSOCKET ) );

    return xSock;
}

uint32_t Prepare_CacheLookup( const char * pcHostName,
                              BaseType_t xFamily,
                              struct freertos_addrinfo ** ppxAddressInfo )
{
    ( *ppxAddressInfo ) = ( struct freertos_addrinfo * ) malloc( sizeof( struct freertos_addrinfo ) );
    __CPROVER_assume( ( *ppxAddressInfo ) != NULL );
    __CPROVER_assume( ( *ppxAddressInfo )->ai_next == NULL );
    uint32_t ulRet;
    return ulRet;
}

/****************************************************************
* The proof for FreeRTOS_gethostbyname_a.
****************************************************************/

void harness()
{
    size_t len;

    pxNetworkEndPoints = ( NetworkEndPoint_t * ) malloc( sizeof( NetworkEndPoint_t ) );
    __CPROVER_assume( pxNetworkEndPoints != NULL );

    /* Asserts are added in the src code to make sure ucDNSIndex
     * will be less than ipconfigENDPOINT_DNS_ADDRESS_COUNT  */
    __CPROVER_assume( pxNetworkEndPoints->ipv6_settings.ucDNSIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT );
    __CPROVER_assume( pxNetworkEndPoints->ipv4_settings.ucDNSIndex < ipconfigENDPOINT_DNS_ADDRESS_COUNT );
    __CPROVER_assume( pxNetworkEndPoints->pxNext == NULL );

    /* Interface init. */
    pxNetworkEndPoints->pxNetworkInterface = ( NetworkInterface_t * ) malloc( sizeof( NetworkInterface_t ) );
    __CPROVER_assume( pxNetworkEndPoints->pxNetworkInterface != NULL );

    __CPROVER_assume( len <= MAX_HOSTNAME_LEN );
    char * pcHostName = safeMalloc( len );

    __CPROVER_assume( len > 0 ); /* prvProcessDNSCache strcmp */
    __CPROVER_assume( pcHostName != NULL );
    pcHostName[ len - 1 ] = NULL;

    FOnDNSEvent pCallback = &func;
    TickType_t xTimeout;
    void * pvSearchID;
    __CPROVER_assume( pvSearchID != NULL );

    FreeRTOS_gethostbyname_a( pcHostName, pCallback, pvSearchID, xTimeout );
}
