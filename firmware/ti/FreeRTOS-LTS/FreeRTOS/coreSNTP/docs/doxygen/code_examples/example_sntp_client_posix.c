#include <stdlib.h>
#include <netdb.h>
#include <time.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <poll.h>
#include <string.h>
#include <assert.h>
#include "core_sntp_client.h"

/* @[code_example_sntpdnsresolve] */
/* Example POSIX implementation of SntpDnsReolve_t interface. */
static bool resolveDns( const SntpServerInfo_t * pServerAddr,
                        uint32_t * pIpV4Addr )
{
    bool status = false;
    int32_t dnsStatus = -1;
    struct addrinfo hints;
    struct addrinfo * pListHead = NULL;

    hints.ai_family = AF_UNSPEC;

    hints.ai_socktype = ( int32_t ) SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    dnsStatus = getaddrinfo( pServerAddr->pServerName, NULL, &hints, &pListHead );

    if( dnsStatus == 0 )
    {
        struct sockaddr_in * pAddrInfo = ( struct sockaddr_in * ) pListHead->ai_addr;
        inet_ntop( pAddrInfo->sin_family,
                   &pAddrInfo->sin_addr,
                   ( int8_t * ) pIpV4Addr,
                   INET_ADDRSTRLEN );

        status = true;
    }

    freeaddrinfo( pListHead );

    return status;
}
/* @[code_example_sntpdnsresolve] */

/* @[code_example_networkcontext] */
/* Example definition of NetworkContext_t for UDP socket operations. */
struct NetworkContext
{
    int udpSocket;
};
/* @[code_example_networkcontext] */

/* @[code_example_udptransport_sendto] */
/* Example POSIX implementation of the UdpTransportSendTo_t function of UDP transport interface. */
static int32_t UdpTransport_Send( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  const void * pBuffer,
                                  uint16_t bytesToSend )
{
    int32_t bytesSent = -1, pollStatus = 1;
    struct pollfd pollFds;

    pollFds.events = POLLOUT | POLLPRI;
    pollFds.revents = 0;
    pollFds.fd = pNetworkContext->udpSocket;

    /* Check if there is data to read from the socket. */
    pollStatus = poll( &pollFds, 1, 0 );

    if( pollStatus > 0 )
    {
        struct sockaddr_in addrInfo;
        addrInfo.sin_family = AF_INET;
        addrInfo.sin_port = htons( serverPort );
        addrInfo.sin_addr.s_addr = htonl( serverAddr );

        bytesSent = sendto( pNetworkContext->udpSocket,
                            pBuffer,
                            bytesToSend, 0,
                            ( const struct sockaddr * ) &addrInfo,
                            sizeof( addrInfo ) );
    }
    else if( pollStatus == 0 )
    {
        bytesSent = 0;
    }

    return bytesSent;
}
/* @[code_example_udptransport_sendto] */

/* @[code_example_udptransport_recvfrom] */
/* Example POSIX implementation of the UdpTransportRecvFrom_t function of UDP transport interface. */
static int32_t UdpTransport_Recv( NetworkContext_t * pNetworkContext,
                                  uint32_t serverAddr,
                                  uint16_t serverPort,
                                  void * pBuffer,
                                  uint16_t bytesToRecv )
{
    int32_t bytesReceived = -1, pollStatus = 1;
    struct pollfd pollFds;

    pollFds.events = POLLIN | POLLPRI;
    pollFds.revents = 0;
    pollFds.fd = pNetworkContext->udpSocket;

    /* Check if there is data to read from the socket. */
    pollStatus = poll( &pollFds, 1, 0 );

    if( pollStatus > 0 )
    {
        struct sockaddr_in addrInfo;
        addrInfo.sin_family = AF_INET;
        addrInfo.sin_port = htons( serverPort );
        addrInfo.sin_addr.s_addr = htonl( serverAddr );
        socklen_t addrLen = sizeof( addrInfo );

        bytesReceived = recvfrom( pNetworkContext->udpSocket, pBuffer,
                                  bytesToRecv, 0,
                                  ( struct sockaddr * ) &addrInfo,
                                  &addrLen );
    }
    else if( pollStatus == 0 )
    {
        bytesReceived = 0;
    }

    return bytesReceived;
}
/* @[code_example_udptransport_recvfrom] */

/* @[code_example_sntpsettime] */
/* Example implementation of the SntpSetTime_t interface for POSIX platforms. */
static void sntpClient_SetTime( const SntpServerInfo_t * pTimeServer,
                                const SntpTimestamp_t * pServerTime,
                                int64_t clockOffsetMs,
                                SntpLeapSecondInfo_t leapSecondInfo )
{
    /* @[code_example_sntp_converttounixtime] */
    uint32_t unixSecs;
    uint32_t unixMs;
    SntpStatus_t status = Sntp_ConvertToUnixTime( pServerTime, &unixSecs, &unixMs );

    /* @[code_example_sntp_converttounixtime] */
    assert( status == SntpSuccess );

    struct timespec serverTime =
    {
        .tv_sec  = unixSecs,
        .tv_nsec = unixMs * 1000
    };

    clock_settime( CLOCK_REALTIME, &serverTime );
}
/* @[code_example_sntpsettime] */

/* @[code_example_sntpgettime] */
/* Example implementation of the SntpGetTime_t interface for POSIX platforms. */
static void sntpClient_GetTime( SntpTimestamp_t * pCurrentTime )
{
    struct timespec currTime;

    ( void ) clock_gettime( CLOCK_REALTIME, &currTime );

    pCurrentTime->seconds = currTime.tv_sec;
    pCurrentTime->fractions = ( currTime.tv_nsec / 1000 ) * SNTP_FRACTION_VALUE_PER_MICROSECOND;
}
/* @[code_example_sntpgettime] */

/* Configuration constants for the example SNTP client. */

/* Following Time Servers are used for illustrating the usage of library API.
 * The library can be configured to use ANY time server, whether publicly available
 * time service like NTP Pool or a privately owned NTP server. */
#define TEST_TIME_SERVER_1                      "0.pool.ntp.org"
#define TEST_TIME_SERVER_2                      "1.pool.ntp.org"

#define SERVER_RESPONSE_TIMEOUT_MS              3000
#define TIME_REQUEST_SEND_WAIT_TIME_MS          2000
#define TIME_REQUEST_RECEIVE_WAIT_TIME_MS       1000

#define SYSTEM_CLOCK_FREQUENCY_TOLERANCE_PPM    500
#define SYSTEM_CLOCK_DESIRED_ACCURACY_MS        300

int main( void )
{
    /* @[code_example_sntp_init] */
    /* Memory for network buffer. */
    uint8_t networkBuffer[ SNTP_PACKET_BASE_SIZE ];

    /* Create UDP socket. */
    NetworkContext_t udpContext;

    udpContext.udpSocket = socket( AF_INET, SOCK_DGRAM, 0 );

    /* Setup list of time servers. */
    SntpServerInfo_t pTimeServers[] =
    {
        {
            .port = SNTP_DEFAULT_SERVER_PORT,
            .pServerName = TEST_TIME_SERVER_1,
            .serverNameLen = strlen( TEST_TIME_SERVER_1 )
        },
        {
            .port = SNTP_DEFAULT_SERVER_PORT,
            .pServerName = TEST_TIME_SERVER_2,
            .serverNameLen = strlen( TEST_TIME_SERVER_2 )
        }
    };

    /* Set the UDP transport interface object. */
    UdpTransportInterface_t udpTransportIntf;

    udpTransportIntf.pUserContext = &udpContext;
    udpTransportIntf.sendTo = UdpTransport_Send;
    udpTransportIntf.recvFrom = UdpTransport_Recv;

    /* Context variable. */
    SntpContext_t context;

    /* Initialize context. */
    SntpStatus_t status = Sntp_Init( &context,
                                     pTimeServers,
                                     sizeof( pTimeServers ) / sizeof( SntpServerInfo_t ),
                                     SERVER_RESPONSE_TIMEOUT_MS,
                                     networkBuffer,
                                     SNTP_PACKET_BASE_SIZE,
                                     resolveDns,
                                     sntpClient_GetTime,
                                     sntpClient_SetTime,
                                     &udpTransportIntf,
                                     NULL );

    assert( status == SntpSuccess );
    /* @[code_example_sntp_init] */

    /* Calculate the polling interval period for the SNTP client. */
    /* @[code_example_sntp_calculatepollinterval] */
    uint32_t pollingIntervalPeriod;

    status = Sntp_CalculatePollInterval( SYSTEM_CLOCK_FREQUENCY_TOLERANCE_PPM,
                                         SYSTEM_CLOCK_DESIRED_ACCURACY_MS,
                                         &pollingIntervalPeriod );
    /* @[code_example_sntp_calculatepollinterval] */
    assert( status == SntpSuccess );

    /* Loop of SNTP client for period time synchronization. */
    /* @[code_example_sntp_send_receive] */
    while( 1 )
    {
        status = Sntp_SendTimeRequest( &context,
                                       rand() % UINT32_MAX,
                                       TIME_REQUEST_SEND_WAIT_TIME_MS );
        assert( status == SntpSuccess );

        do
        {
            status = Sntp_ReceiveTimeResponse( &context, TIME_REQUEST_RECEIVE_WAIT_TIME_MS );
        } while( status == SntpNoResponseReceived );

        assert( status == SntpSuccess );

        /* Delay of poll interval period before next time synchronization. */
        sleep( pollingIntervalPeriod );
    }

    /* @[code_example_sntp_send_receive] */

    return EXIT_SUCCESS;
}
