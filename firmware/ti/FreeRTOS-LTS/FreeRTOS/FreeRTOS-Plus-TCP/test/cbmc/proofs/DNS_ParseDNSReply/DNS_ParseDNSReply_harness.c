/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_DNS_Parser.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"
#include "IPTraceMacroDefaults.h"

#include "cbmc.h"
#include "../../utility/memory_assignments.c"

/****************************************************************
* Signature of function under test
****************************************************************/

uint32_t DNS_ParseDNSReply( uint8_t * pucUDPPayloadBuffer,
                            size_t uxBufferLength,
                            struct freertos_addrinfo ** ppxAddressInfo,
                            BaseType_t xExpected,
                            uint16_t usPort );

NetworkBufferDescriptor_t xNetworkBuffer;
int lIsIPv6Packet;

size_t uxIPHeaderSizePacket( const NetworkBufferDescriptor_t * pxNetworkBuffer )
{
    #if IS_TESTING_IPV6
        return ipSIZE_OF_IPv6_HEADER;
    #else
        return ipSIZE_OF_IPv4_HEADER;
    #endif
}

NetworkBufferDescriptor_t * pxUDPPayloadBuffer_to_NetworkBuffer( const void * pvBuffer )
{
    __CPROVER_assert( pvBuffer != NULL, "Precondition: pvBuffer != NULL" );
    NetworkBufferDescriptor_t * pxRBuf;

    if( nondet_bool() )
    {
        pxRBuf = NULL;
    }
    else
    {
        pxRBuf = &xNetworkBuffer;
    }

    return pxRBuf;
}

uint32_t ulChar2u32( const uint8_t * pucPtr )
{
    __CPROVER_assert( __CPROVER_r_ok( pucPtr, 4 ), "must be 4 bytes legal address to read" );
}

uint16_t usChar2u16( const uint8_t * pucPtr )
{
    __CPROVER_assert( __CPROVER_r_ok( pucPtr, 2 ), "must be 2 bytes legal address to read" );
}

const char * FreeRTOS_inet_ntop( BaseType_t xAddressFamily,
                                 const void * pvSource,
                                 char * pcDestination,
                                 socklen_t uxSize )
{
    __CPROVER_assert( __CPROVER_r_ok( pcDestination, uxSize ), "input buffer must be available" );

    #if IS_TESTING_IPV6
        __CPROVER_assert( ( xAddressFamily == FREERTOS_AF_INET6 && __CPROVER_r_ok( pvSource, 16 ) ), "input address must be available" );
    #else
        __CPROVER_assert( ( xAddressFamily == FREERTOS_AF_INET && __CPROVER_r_ok( pvSource, 4 ) ), "input address must be available" );
    #endif
}

BaseType_t xApplicationDNSQueryHook_Multi( struct xNetworkEndPoint * pxEndPoint,
                                           const char * pcName )
{
    __CPROVER_assert( strlen( pcName ) < ipconfigDNS_CACHE_NAME_LENGTH, "The length of domain name must be less than cache size" );
}

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    __CPROVER_assert( pxNetworkBuffer, "network descriptor must be valid." );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer, "network buffer must be valid." );

    free( pxNetworkBuffer->pucEthernetBuffer );
    free( pxNetworkBuffer );
}

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateChecksum( uint16_t usSum,
                             const uint8_t * pucNextData,
                             size_t uxByteCount )
{
    uint16_t usReturn;

    __CPROVER_assert( __CPROVER_r_ok( pucNextData, uxByteCount ), "Data must be valid" );

    /* Return an indeterminate value. */
    return usReturn;
}

/* The checksum generation is stubbed out since the actual checksum
 * does not matter. The stub will return an indeterminate value each time. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer,
                                     size_t uxBufferLength,
                                     BaseType_t xOutgoingPacket )
{
    uint16_t usReturn;

    __CPROVER_assert( __CPROVER_r_ok( pucEthernetBuffer, uxBufferLength ), "Data must be valid" );

    /* Return an indeterminate value. */
    return usReturn;
}

/* pxDuplicateNetworkBufferWithDescriptor() is proved separately */
NetworkBufferDescriptor_t * pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                                                    size_t xNewLength )
{
    NetworkBufferDescriptor_t * pxNetworkBuffer = safeMalloc( sizeof( NetworkBufferDescriptor_t ) );

    if( ensure_memory_is_valid( pxNetworkBuffer, xNewLength ) )
    {
        pxNetworkBuffer->pucEthernetBuffer = safeMalloc( xNewLength );
        __CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer );
        pxNetworkBuffer->xDataLength = xNewLength;
    }

    return pxNetworkBuffer;
}

/* vReturnEthernetFrame() is proved separately */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer,
                           BaseType_t xReleaseAfterSend )
{
    __CPROVER_assert( pxNetworkBuffer != NULL, "xNetworkBuffer != NULL" );
    __CPROVER_assert( pxNetworkBuffer->pucEthernetBuffer != NULL, "pxNetworkBuffer->pucEthernetBuffer != NULL" );
    __CPROVER_assert( __CPROVER_r_ok( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength ), "Data must be valid" );
}

uint32_t parseDNSAnswer( ParseSet_t * pxSet,
                         struct freertos_addrinfo ** ppxAddressInfo,
                         size_t * uxBytesRead )
{
    uint32_t result;

    __CPROVER_assert( __CPROVER_r_ok( pxSet->pucByte, pxSet->uxSourceBytesRemaining ), "Data must be valid" );

    return result;
}

/****************************************************************
* Proof of prvParseDNSReply
****************************************************************/

void harness()
{
    size_t uxBufferLength;
    uint16_t usPort;
    struct freertos_addrinfo * pxAddressInfo;
    BaseType_t xExpected;
    NetworkEndPoint_t * pxNetworkEndPoint_Temp = ( NetworkEndPoint_t * ) safeMalloc( sizeof( NetworkEndPoint_t ) );
    const uint32_t ulIpv4UdpOffset = 42, ulIpv6UdpOffset = 62;
    uint8_t * pPayloadBuffer;
    size_t uxPayloadBufferLength;

    __CPROVER_assert( TEST_PACKET_SIZE < CBMC_MAX_OBJECT_SIZE,
                      "TEST_PACKET_SIZE < CBMC_MAX_OBJECT_SIZE" );

    __CPROVER_assume( uxBufferLength < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( uxBufferLength <= TEST_PACKET_SIZE );

    lIsIPv6Packet = IS_TESTING_IPV6;

    xNetworkBuffer.pucEthernetBuffer = safeMalloc( uxBufferLength );
    xNetworkBuffer.xDataLength = uxBufferLength;
    xNetworkBuffer.pxEndPoint = pxNetworkEndPoint_Temp;

    __CPROVER_assume( xNetworkBuffer.pucEthernetBuffer != NULL );

    if( lIsIPv6Packet )
    {
        __CPROVER_assume( uxBufferLength >= ulIpv6UdpOffset ); /* 62 is total size of IPv4 UDP header, including ethernet, IPv6, UDP headers. */
        pPayloadBuffer = xNetworkBuffer.pucEthernetBuffer + ulIpv6UdpOffset;
        uxPayloadBufferLength = uxBufferLength - ulIpv6UdpOffset;
    }
    else
    {
        __CPROVER_assume( uxBufferLength >= ulIpv4UdpOffset ); /* 42 is total size of IPv4 UDP header, including ethernet, IPv4, UDP headers. */
        pPayloadBuffer = xNetworkBuffer.pucEthernetBuffer + ulIpv4UdpOffset;
        uxPayloadBufferLength = uxBufferLength - ulIpv4UdpOffset;
    }

    uint32_t index = DNS_ParseDNSReply( pPayloadBuffer,
                                        uxPayloadBufferLength,
                                        &pxAddressInfo,
                                        xExpected,
                                        usPort );
}
