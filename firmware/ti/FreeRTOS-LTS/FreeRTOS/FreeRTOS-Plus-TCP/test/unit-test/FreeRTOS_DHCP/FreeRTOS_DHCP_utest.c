/* Include Unity header */
#include "unity.h"

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mock_FreeRTOS_IP.h"
#include "mock_FreeRTOS_IP_Timers.h"
#include "mock_FreeRTOS_IP_Private.h"
#include "mock_FreeRTOS_Sockets.h"
#include "mock_FreeRTOS_UDP_IP.h"
#include "mock_FreeRTOS_ARP.h"
#include "mock_task.h"
#include "mock_NetworkBufferManagement.h"
#include "mock_FreeRTOS_DHCP_mock.h"
#include "mock_FreeRTOS_IP_Common.h"

#include "FreeRTOS_DHCP.h"

#include "FreeRTOS_DHCP_stubs.c"
#include "catch_assert.h"

#include "FreeRTOSIPConfig.h"

/*-------------------------------------Extern Variables--------------------------*/

void vDHCPProcessEndPoint( BaseType_t xReset,
                           BaseType_t xDoCheck,
                           NetworkEndPoint_t * pxEndPoint );
BaseType_t xProcessCheckOption( ProcessSet_t * pxSet );

extern Socket_t xDHCPv4Socket;
extern DHCPData_t xDHCPData;

extern NetworkInterface_t xInterfaces[ 1 ];
extern BaseType_t xDHCPSocketUserCount;


static const char * pcHostName = "Unit-Test";

extern eDHCPCallbackPhase_t eStubExpectedDHCPPhase;
extern struct xNetworkEndPoint * pxStubExpectedEndPoint;
extern uint32_t ulStubExpectedIPAddress;
extern eDHCPCallbackAnswer_t eStubExpectedReturn;
extern uint8_t * ucGenericPtr;
extern int32_t ulGenericLength;
extern NetworkBufferDescriptor_t * pxGlobalNetworkBuffer[ 10 ];
extern uint8_t GlobalBufferCounter;

extern uint8_t pucUDPBuffer[];

extern uint8_t DHCP_header[];

/*-------------------------------------Helpers--------------------------------*/

static void prvWriteDHCPOption( uint8_t ** ppucBuf,
                                uint8_t ucOp,
                                const void * pvPayload,
                                uint8_t ucLen )
{
    uint8_t * pucBuf = *ppucBuf;

    *pucBuf++ = ucOp;
    *pucBuf++ = ucLen;
    memcpy( pucBuf, pvPayload, ucLen );
    pucBuf += ucLen;

    *ppucBuf = pucBuf;
}

static void prvWriteDHCPOptionU8( uint8_t ** ppucBuf,
                                  uint8_t ucOp,
                                  uint8_t ucPayload )
{
    prvWriteDHCPOption( ppucBuf, ucOp, &ucPayload, sizeof( ucPayload ) );
}

static void prvWriteDHCPOptionU32( uint8_t ** ppucBuf,
                                   uint8_t ucOp,
                                   uint32_t ulPayload )
{
    /* TBD: htonl(ulPayload)? */
    prvWriteDHCPOption( ppucBuf, ucOp, &ulPayload, sizeof( ulPayload ) );
}

/*---------------------------------------Test Cases--------------------------*/
void test_xIsDHCPSocket( void )
{
    BaseType_t xReturn;
    struct xSOCKET xTestSocket;

    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;

    /************************************/
    /* Test by NOT giving DHCP socket. */
    xReturn = xIsDHCPSocket( NULL );
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );

    /************************************/
    /* Test by giving DHCP socket. */
    xReturn = xIsDHCPSocket( xDHCPv4Socket );
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    xDHCPv4Socket = NULL;
}

void test_vDHCPProcess_AssertChecks( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 };

    xEndPoint.bits.bIPv6 = 1;
    catch_assert( vDHCPProcess( pdFALSE, NULL ) );
    catch_assert( vDHCPProcess( pdFALSE, &xEndPoint ) );
}

void test_vDHCPProcess_NotResetAndIncorrectState( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Since the expected state is incorrect, the state
     * should remain the same. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGFail( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    /* Make random number generation fail. */
    xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdFALSE );
    vDHCPProcess( pdTRUE, pxEndPoint );

    /* Expected state is incorrect, but we are trying to reset
     * the DHCP the state machine. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_ResetAndInvalidSocket( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;
    /* Put any state. */
    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = 0;
    /* This should be reset to 0. */
    pxEndPoint->xDHCPData.xUseBroadcast = 1;
    /* This should be reset as well */
    pxEndPoint->xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
    /* And this too. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = 0xABABABAB;

    /* Make random number generation pass. */
    xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdTRUE );
    /* return an invalid socket. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, FREERTOS_INVALID_SOCKET );

    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    catch_assert( vDHCPProcess( pdTRUE, pxEndPoint ) );
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketCreationFail( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    int i;

    /* Test all the valid and invalid entries. */
    for( i = 0; i < ( eNotUsingLeasedAddress * 2 ); i++ )
    {
        /* This should get assigned to a given value. */
        xDHCPv4Socket = NULL;
        pxEndPoint->xDHCPData.xDHCPSocket = NULL;
        /* Put any state. */
        pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
        pxEndPoint->xDHCPData.eExpectedState = i;
        /* This should be reset to 0. */
        pxEndPoint->xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        pxEndPoint->xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        pxEndPoint->xDHCPData.ulDHCPServerAddress = 0xABABABAB;

        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdTRUE );
        /* return an invalid socket. */
        FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, FREERTOS_INVALID_SOCKET );

        xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
        xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

        /* See if the timer is reloaded. */
        vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, pxEndPoint );

        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
        TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.xUseBroadcast );
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulOfferedIPAddress );
        /* And this too. */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulDHCPServerAddress );
    }
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketSuccess( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    int i;

    /* Test all the valid and invalid entries. */
    for( i = 0; i < ( eNotUsingLeasedAddress * 2 ); i++ )
    {
        /* This should get assigned to a given value. */
        xDHCPv4Socket = NULL;
        pxEndPoint->xDHCPData.xDHCPSocket = NULL;
        /* Put any state. */
        pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
        pxEndPoint->xDHCPData.eExpectedState = i;
        /* This should be reset to 0. */
        pxEndPoint->xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        pxEndPoint->xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        pxEndPoint->xDHCPData.ulDHCPServerAddress = 0xABABABAB;


        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdTRUE );
        /* Return a valid socket. */
        FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xTestSocket );

        xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
        xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

        /* Ignore the inputs to setting the socket options. */
        FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
        FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
        /* Make sure that binding passes. Return zero. */
        vSocketBind_ExpectAnyArgsAndReturn( 0 );
        /* See if the timer is reloaded. */
        vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, pxEndPoint );

        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
        TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.xUseBroadcast );
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulOfferedIPAddress );
        /* And this too. */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulDHCPServerAddress );
    }
}

void test_vDHCPProcess_ResetAndIncorrectStateWithRNGSuccessSocketBindFail( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    int i;

    /* Test all the valid and invalid entries. */
    for( i = 0; i < ( eNotUsingLeasedAddress * 2 ); i++ )
    {
        /* This should remain unchanged. */
        xDHCPv4Socket = NULL;
        pxEndPoint->xDHCPData.xDHCPSocket = NULL;
        /* Put any state. */
        pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
        pxEndPoint->xDHCPData.eExpectedState = i;
        /* This should be reset to 0. */
        pxEndPoint->xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        pxEndPoint->xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        pxEndPoint->xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdTRUE );
        /* Return a valid socket. */
        FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xTestSocket );

        xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
        xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

        /* Ignore the inputs to setting the socket options. */
        FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
        FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
        /* Make sure that binding fails. Return anything except zero. */
        vSocketBind_ExpectAnyArgsAndReturn( 1 );
        /* Expect the socket to be closed. */
        vSocketClose_ExpectAndReturn( &xTestSocket, NULL );
        /* See if the timer is reloaded. */
        vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, pxEndPoint );
    }
}

void test_vDHCPProcess_ResetAndIncorrectStateWithSocketAlreadyCreated( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    int i;

    /* Test all the valid and invalid entries. */
    for( i = 0; i < ( eNotUsingLeasedAddress * 2 ); i++ )
    {
        /* This should remain unchanged. */
        xDHCPv4Socket = &xTestSocket;
        xDHCPSocketUserCount = 1;
        pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
        /* Put any state. */
        pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
        pxEndPoint->xDHCPData.eExpectedState = i;
        /* This should be reset to 0. */
        pxEndPoint->xDHCPData.xUseBroadcast = 1;
        /* This should be reset as well */
        pxEndPoint->xDHCPData.ulOfferedIPAddress = 0xAAAAAAAA;
        /* And this too. */
        pxEndPoint->xDHCPData.ulDHCPServerAddress = 0xABABABAB;
        /* And this should be updated. */
        pxEndPoint->xDHCPData.xDHCPTxPeriod = 0;

        /* Expect these arguments. */
        FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
        /* Ignore the buffer argument though. */
        FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
        /* Make random number generation pass. */
        xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint->xDHCPData.ulTransactionId ), pdTRUE );
        /* See if the timer is reloaded. */
        vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );
        /* Try all kinds of states. */
        vDHCPProcess( pdTRUE, pxEndPoint );

        /* Expected state is incorrect, but we are trying to reset
         * the DHCP the state machine. */
        TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
        TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
        TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.xUseBroadcast );
        /* This should be reset as well */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulOfferedIPAddress );
        /* And this too. */
        TEST_ASSERT_EQUAL( 0, pxEndPoint->xDHCPData.ulDHCPServerAddress );
        /* This should be updated. */
        TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD, pxEndPoint->xDHCPData.xDHCPTxPeriod );
    }
}

void test_vDHCPProcess_CorrectStateDHCPHookFailsDHCPSocketNULL( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* The DHCP socket is NULL. */
    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    pxEndPoint->ipv4_defaults.ulIPAddress = 0x12345678;

    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = ( eDHCPContinue + eDHCPUseDefaults ) << 2;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Ignore();

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that the Endpoint IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( pxEndPoint->ipv4_defaults.ulIPAddress, pxEndPoint->ipv4_settings.ulIPAddress );
}

void test_vDHCPProcess_CorrectStateDHCPHookFailsDHCPSocketNonNULL( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    pxEndPoint->ipv4_defaults.ulIPAddress = 0x12345678;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = ( eDHCPContinue + eDHCPUseDefaults ) << 2;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPv4Socket, NULL );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that the local IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( pxEndPoint->ipv4_defaults.ulIPAddress, pxEndPoint->ipv4_settings.ulIPAddress );
}

void test_vDHCPProcess_CorrectStateDHCPHookDefaultReturn( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPUseDefaults;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPv4Socket, NULL );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that the network addressing struct is updated to show that. */
    TEST_ASSERT_EQUAL_MEMORY( &pxEndPoint->ipv4_defaults, &pxEndPoint->ipv4_settings, sizeof( IPV4Parameters_t ) );
    /* Make sure that the local IP address pointer indicates that. */
    TEST_ASSERT_EQUAL( pxEndPoint->ipv4_defaults.ulIPAddress, pxEndPoint->ipv4_settings.ulIPAddress );
}

/* GNW = getNetworkBufferWithDescriptor */
void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnDHCPSocketNotNULLButGNWFails( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    xTaskGetTickCount_ExpectAndReturn( 100 );
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnDHCPSocketNotNULLButHostNameNULL( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    xTaskGetTickCount_ExpectAndReturn( 100 );
    pcApplicationHostnameHook_ExpectAndReturn( NULL );
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnDHCPSocketNULL( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;

    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    /* Ignore the call. */
    vIPNetworkUpCalls_Ignore();

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we are not using leased address. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendFailsNoBroadcast( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Not using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send fail. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendFailsNoBroadcast_NULLHostName( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Not using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname = NULL. */
    pcApplicationHostnameHook_ExpectAndReturn( NULL );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send fail. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendFailsUseBroadCast( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Not using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdTRUE;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    /* Make the call to FreeRTOS_send fail. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 0 );
    /* Since the send failed, a call to release the buffer should be there. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingSendFirstDiscover, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendSucceedsUseBroadCast( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdTRUE;
    pxEndPoint->xDHCPData.ulPreferredIPAddress = 0x00;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send succeed. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );

    /* Free the allocated memory. */
    ReleaseNetworkBuffer();
}

void test_vDHCPProcess_CorrectStateDHCPHookContinueReturnSendSucceedsUseBroadCast1( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingSendFirstDiscover;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingSendFirstDiscover;
    /* Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdTRUE;
    pxEndPoint->xDHCPData.ulPreferredIPAddress = 0x01;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Make sure that the user indicates anything else than the desired options. */
    eStubExpectedDHCPPhase = eDHCPPhasePreDiscover;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send succeed. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be as expected. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );

    /* Free the allocated memory. */
    ReleaseNetworkBuffer();
}

void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWFails( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = eSendDHCPRequest;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Return NULL network buffer. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be NULL */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWSucceedsSendFails( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = eSendDHCPRequest;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Send fails. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 0 );
    /* ReleaseUDPPayloadBuffer will be called. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Stub( ReleaseUDPBuffer );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eSendDHCPRequestCorrectStateGNWSucceedsSendSucceeds( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eSendDHCPRequest;
    pxEndPoint->xDHCPData.eExpectedState = eSendDHCPRequest;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();
    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );
    /* Return the time value. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
    TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be still allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutGiveUp( void ) /* prvCloseDHCPSocket */
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we exceed the period - and give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ipconfigMAXIMUM_DISCOVER_TX_PERIOD;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    /* Time will be stored in DHCP state machine. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );


    /* Closing the DHCP socket. */
    vSocketClose_ExpectAndReturn( xDHCPv4Socket, 0 );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    /* Ignore the call to this function. */
    vARPSendGratuitous_Ignore();

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGFail( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1;

    /* Expect these arguments. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    /* Make all calls to the RNG fail. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ( ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1 ) << 1, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGPassUseBroadcast( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1;
    /* Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdTRUE;

    /* Expect these arguments. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ( ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1 ) << 1, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

void test_vDHCPProcess_eWaitingOfferRecvfromFailsTimeoutDontGiveUpRNGPassNoBroadcast( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;

    /* Expect these arguments. Return a 0 to fail. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY + FREERTOS_MSG_PEEK, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference greater than the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    /* Make all calls to the RNG succeed. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a NULL network buffer. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eInitialWait, pxEndPoint->xDHCPData.eDHCPState );
    /* make sure that the period is increased by a factor of two. */
    TEST_ASSERT_EQUAL( ( ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) - 1 ) << 1, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

/**
 *@brief  This function ensures if bytes is received in the next UDP message
 */

void test_vDHCPProcess_eLeasedAddress_CorrectState_ValidBytesInMessage( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_CorrectState_ValidBytesInMessage_TransactionIDMismatch( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    /* make sure the transaction ID does not match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEE;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;
    pxNetworkEndPoints->pxNext = NULL;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_CorrectState_ValidBytesInMessage_TwoFlagOptions_nullbytes( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage_TwoFlagOptions_nullbytes );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_CorrectState_ValidBytesInMessage_TwoFlagOptions_nullbuffer( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage_TwoFlagOptions_nullbuffer );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_IncorrectDHCPCookie_ValidBytesInMessage( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage_IncorrectDHCPCookie );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_IncorrectOpCode_ValidBytesInMessage( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage_IncorrectOpCode );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

/**
 *@brief  This function ensures if bytes is received in the next UDP message
 *        when DHCP state is eWaitingOffer
 */

void test_vDHCPProcess_eWaitingOffer_CorrectState_ValidBytesInMessage_MatchingEndPoint( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage );

    FreeRTOS_ReleaseUDPPayloadBuffer_Ignore();

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

/**
 *@brief  This function ensures if bytes is received in the next UDP message
 *        when DHCP state is eWaitingAcknowledge
 */

void test_vDHCPProcess_eWaitingAcknowledge_CorrectState_ValidBytesInMessage_diffEndPoint( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    NetworkEndPoint_t xEndPoint_2 = { 0 }, * pxEndPoint_2 = &xEndPoint_2;
    uint8_t * pucUDPPayload;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_settings, 0xAA, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint->ipv4_defaults, 0xBB, sizeof( IPV4Parameters_t ) );

    /* Put the required state. */
    pxEndPoint_2->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint_2->xDHCPData.eExpectedState = eWaitingAcknowledge;
    pxEndPoint_2->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Make sure that the local IP address is uninitialised. */
    pxEndPoint_2->ipv4_settings.ulIPAddress = 0;
    /* Put a verifiable value. */
    memset( &pxEndPoint_2->ipv4_settings, 0xBB, sizeof( IPV4Parameters_t ) );
    /* Put a verifiable value. */
    memset( &pxEndPoint_2->ipv4_defaults, 0xAA, sizeof( IPV4Parameters_t ) );

    pxNetworkEndPoints = pxEndPoint_2;
    pxEndPoint_2->pxNext = pxEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Expect these arguments. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_ResetAndIncorrectStateWithSocketAlreadyCreated_validUDPmessage_TwoFlagOptions_nullbytes );
    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime );

    vDHCPProcess( pdFALSE, pxEndPoint );

    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcessEndPoint_NullEndPoint( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    pxEndPoint->xDHCPData.ulTransactionId = 0;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout );

    catch_assert( vDHCPProcessEndPoint( pdFALSE, pdTRUE, NULL ) );
}

void test_vDHCPProcessEndPoint_eWaitingOfferNullUDPBuffer( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    pxEndPoint->xDHCPData.ulTransactionId = 0;

    pxNetworkEndPoints = pxEndPoint;

    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Small_NullBuffer );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );
}

void test_vDHCPProcessEndPoint_eWaitingOfferDHCPReply_NullUDPmessage( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    pxEndPoint->xDHCPData.ulTransactionId = 0;

    pxNetworkEndPoints = pxEndPoint;
    /*  Expect these arguments. */
    FreeRTOS_recvfrom_ExpectAndReturn( xDHCPv4Socket, NULL, 0UL, FREERTOS_ZERO_COPY, NULL, NULL, 0 );
    /* Ignore the buffer argument though. */
    FreeRTOS_recvfrom_IgnoreArg_pvBuffer();

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    pxEndPoint->xDHCPData.ulTransactionId = 0;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseCookieNoTimeout );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsFalseOpcodeNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsFalseOpcodeNoTimeout );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSucceedsCorrectCookieAndOpcodeNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which won't match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSucceedsCorrectCookieAndOpcodeNoTimeout );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromLessBytesNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which won't match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromLessBytesNoTimeout );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccessCorrectTxID( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccessCorrectTxID );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccess_CorrectAddrType( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccess_CorrectAddrType );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccess_CorrectAddrLen_BroadcastAddress( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccess_CorrectAddrLen );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccess_CorrectAddrLen_LocalHostAddress( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccess_LocalHostAddr );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccess_CorrectAddrLen_NonLocalHostAddress( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccess_NonLocalHostAddr );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferRecvfromSuccess_CorrectAddrLen_LocalMACNotmatching( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    MACAddress_t xBackup;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    memcpy( &xBackup, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_eWaitingOfferRecvfromSuccess_LocalMACAddrNotMatching );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( pucUDPBuffer );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageWithoutOptionsNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    uint8_t DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageIncorrectOptionsNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 3U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Now add options which will be processed. */
    /* Add a closing flag at the end. */
    DHCPMsg[ xTotalLength - 1U ] = 0xFF;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageMissingLengthByteNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageIncorrectLengthByteNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add incorrect length. */
    DHCPOption[ 1 ] = 100;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageGetNACKNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_NACK;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageGetNACKNoTimeout_MatchingMACAddress( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_NACK;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Set the MAC address that matches. */
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageGetACKNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageOneOptionNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageOneOptionNoTimeout2( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U + 3U + 1U;
    uint8_t DHCPMsg[ xTotalLength ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_DNS_SERVER_OPTIONS_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = 12;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    /*xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod ); */

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that we still in the state from where we started. */
    TEST_ASSERT_EQUAL( eWaitingOffer, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageTwoOptionsSendFails( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.ulOfferedIPAddress = DHCPServerAddress;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Make sure that the address matches. */
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );
    /* Return continue. */
    eStubExpectedDHCPPhase = eDHCPPhasePreRequest;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = ulClientIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Make the hook return correct value. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning NULL will mean the prvSendDHCPRequest fails. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that sending failed. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageTwoOptionsSendSucceeds( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.ulOfferedIPAddress = DHCPServerAddress;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );
    /* Return continue. */
    eStubExpectedDHCPPhase = eDHCPPhasePreRequest;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = ulClientIPAddress;
    eStubExpectedReturn = eDHCPContinue;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Make the hook return correct value. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send succeed. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that sending failed. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    /* The time should be updated. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageTwoOptionsDHCPHookReturnDefaultSendSucceeds( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.ulOfferedIPAddress = DHCPServerAddress;

    /* Rest the network addressing values. */
    memset( &( pxEndPoint->ipv4_settings ), 0, sizeof( IPV4Parameters_t ) );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;

    pxNetworkEndPoints = pxEndPoint;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );
    /* Return continue. */
    eStubExpectedDHCPPhase = eDHCPPhasePreRequest;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = ulClientIPAddress;
    eStubExpectedReturn = eDHCPUseDefaults;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPv4Socket, NULL );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that sending failed. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( &( pxEndPoint->ipv4_settings ), &( pxEndPoint->ipv4_defaults ), sizeof( IPV4Parameters_t ) );
}

void test_vDHCPProcess_eWaitingOfferCorrectDHCPMessageTwoOptionsDHCPHookReturnErrorSendSucceeds( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint8_t testMemory[ sizeof( IPV4Parameters_t ) ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;

    pxEndPoint->xDHCPData.ulOfferedIPAddress = DHCPServerAddress;

    /* Rest the network addressing values. */
    memset( &( xEndPoint ), 0, sizeof( NetworkEndPoint_t ) );
    memset( &( testMemory ), 0, sizeof( IPV4Parameters_t ) );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingOffer;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingOffer;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Make sure that the address matches. */
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );


    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );
    /* Return continue. */
    eStubExpectedDHCPPhase = eDHCPPhasePreRequest;
    pxStubExpectedEndPoint = pxEndPoint;
    ulStubExpectedIPAddress = ulClientIPAddress;
    eStubExpectedReturn = ( eDHCPContinue + eDHCPUseDefaults ) << 1;
    xApplicationDHCPHook_Multi_Stub( xStubApplicationDHCPHook_Multi );
    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );
    vIPNetworkUpCalls_Ignore();
    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( xDHCPv4Socket, NULL );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* The state should indicate that sending failed. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( &( pxEndPoint->ipv4_settings ), &( testMemory ), sizeof( IPV4Parameters_t ) );
}


void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsIncorrectServerNoTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint8_t testMemory[ sizeof( IPV4Parameters_t ) ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Rest the network addressing values. */
    memset( &( pxEndPoint->ipv4_settings ), 0, sizeof( IPV4Parameters_t ) );
    memset( &( testMemory ), 0, sizeof( IPV4Parameters_t ) );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put incorrect address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress + 1234;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Still waiting on acknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL_MEMORY( &( pxEndPoint->ipv4_settings ), &( testMemory ), sizeof( IPV4Parameters_t ) );
}

void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsIncorrectServerTimeoutGNBfails( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint8_t testMemory[ sizeof( IPV4Parameters_t ) ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Rest the network addressing values. */
    memset( &( pxEndPoint->ipv4_settings ), 0, sizeof( IPV4Parameters_t ) );
    memset( &( testMemory ), 0, sizeof( IPV4Parameters_t ) );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put incorrect address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress + 1234;

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );
    /* Return time second time which can be verified. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a NULL so that prvSendDHCPRequest fails. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Still waiting on acknowledge. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
    /* The time value should be stored in the state machine. */
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
    TEST_ASSERT_EQUAL_MEMORY( &( pxEndPoint->ipv4_settings ), &( testMemory ), sizeof( IPV4Parameters_t ) );
}

void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsIncorrectServerTimeoutGNBSucceeds( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put incorrect address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress + 1234;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );
    /* Return time second time which can be verified. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

    /* Send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Still waiting on acknowledge. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsIncorrectServerTimeoutPeriodLess( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure we exceed the period - and thus, give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) + 1;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put incorrect address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress + 1234;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Period exceeded. We should now be in initial state. */
    TEST_ASSERT_EQUAL( eInitialWait, pxEndPoint->xDHCPData.eDHCPState );
    /* Period exceeded, should have initial value */
    TEST_ASSERT_EQUAL( 100, pxEndPoint->xDHCPData.xDHCPTxTime );
}

void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsIncorrectServerTimeoutPeriodLessTimeout( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure we exceed the period - and thus, give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = ( ipconfigMAXIMUM_DISCOVER_TX_PERIOD >> 1 ) + 1;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put incorrect address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress + 1234;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    /* Make sure that there is timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod );

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Period exceeded. We should now be in initial state. */
    /* Period exceeded, should have initial value */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( 100, pxEndPoint->xDHCPData.xDHCPTxTime );
}


void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsCorrectServerLeaseTimeZero( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Make sure that the address matches. */
    memcpy( pxEndPoint->xMACAddress.ucBytes, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );

    /* Reset the lease time so that it will be set to default
     * value later. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpDEFAULT_LEASE_TIME );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eWaitingAcknowledgeTwoOptionsCorrectServerLeaseTimeLessThanMinConfig( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;

    /* Reset the lease time so that it will be set to minimum
     * value later. */
    pxEndPoint->xDHCPData.ulLeaseTime = dhcpMINIMUM_LEASE_TIME - 10;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpMINIMUM_LEASE_TIME );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( dhcpMINIMUM_LEASE_TIME, pxEndPoint->xDHCPData.ulLeaseTime );
}


void test_vDHCPProcess_eWaitingAcknowledge_TwoOptions_CorrectServer_AptLeaseTime( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time to an appropriate value. */
    pxEndPoint->xDHCPData.ulLeaseTime = dhcpMINIMUM_LEASE_TIME + 10;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpMINIMUM_LEASE_TIME + 10 );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( dhcpMINIMUM_LEASE_TIME + 10, pxEndPoint->xDHCPData.ulLeaseTime );
}

void test_vDHCPProcess_eWaitingAcknowledge_TwoOptions_NACK( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_NACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time to an appropriate value. */
    pxEndPoint->xDHCPData.ulLeaseTime = dhcpMINIMUM_LEASE_TIME + 10;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be reset after NACK. */
    TEST_ASSERT_EQUAL( eInitialWait, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eWaitingAcknowledge_TwoOptions_OFFER( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */ + 3U /* DHCP offer */ + 6U /* Server IP address */ + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_OFFER;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time to an appropriate value. */
    pxEndPoint->xDHCPData.ulLeaseTime = dhcpMINIMUM_LEASE_TIME + 10;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should not be reset after OFFER. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eWaitingAcknowledge_AllOptionsCorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 6U                                    /* DNS server */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );

    DHCPMsg[ xTotalLength - 1U ] = 0xFF;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SUBNET_MASK_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulSubnetMask, sizeof( ulSubnetMask ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_GATEWAY_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulGateway, sizeof( ulGateway ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_LEASE_TIME_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulLeaseTime, sizeof( ulLeaseTime ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_DNS_SERVER_OPTIONS_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulDNSServer, sizeof( ulDNSServer ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}

void test_vDHCPProcess_eWaitingAcknowledge_AllOptionsCorrectLength2( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 6U                                    /* DNS server */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );

    DHCPMsg[ xTotalLength - 1U ] = 0xFF;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SUBNET_MASK_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulSubnetMask, sizeof( ulSubnetMask ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_GATEWAY_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulGateway, sizeof( ulGateway ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_LEASE_TIME_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulLeaseTime, sizeof( ulLeaseTime ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_DNS_SERVER_OPTIONS_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulDNSServer, sizeof( ulDNSServer ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}


void test_vDHCPProcess_eWaitingAcknowledge_DNSIncorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 6U                                    /* DNS server */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );

    DHCPMsg[ xTotalLength - 1U ] = 0xFF;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SUBNET_MASK_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulSubnetMask, sizeof( ulSubnetMask ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_GATEWAY_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulGateway, sizeof( ulGateway ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_LEASE_TIME_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulLeaseTime, sizeof( ulLeaseTime ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_DNS_SERVER_OPTIONS_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 3;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulDNSServer, sizeof( ulDNSServer ) );


    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}

void test_vDHCPProcess_eWaitingAcknowledge_DNSServerOverabundance( void )
{
    struct xSOCKET xTestSocket;

    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    uint8_t DHCPMsg[
        sizeof( DHCPMessage_IPv4_t )
        + 2U + sizeof( ( uint8_t ) dhcpMESSAGE_TYPE_ACK )
        + 2U + sizeof( DHCPServerAddress )
        + 2U + sizeof( ulSubnetMask )
        + 2U + sizeof( ulGateway )
        + 2U + sizeof( ulLeaseTime )
        + 2U + sizeof( ulDNSServer ) * ( ipconfigENDPOINT_DNS_ADDRESS_COUNT + 1 )
    ];
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );
    size_t xDNSServersToAdd = ipconfigENDPOINT_DNS_ADDRESS_COUNT + 1;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    uint8_t * DHCPOption = &DHCPMsg[ sizeof( DHCPMessage_IPv4_t ) ];

    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 3;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SUBNET_MASK_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulSubnetMask, sizeof( ulSubnetMask ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_GATEWAY_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulGateway, sizeof( ulGateway ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_LEASE_TIME_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulLeaseTime, sizeof( ulLeaseTime ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_DNS_SERVER_OPTIONS_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = xDNSServersToAdd * sizeof( ulDNSServer );
    DHCPOption += 2;

    while( xDNSServersToAdd-- > 0U )
    {
        memcpy( DHCPOption, &ulDNSServer, sizeof( ulDNSServer ) );
        DHCPOption += sizeof( ulDNSServer );
    }

    /* A stop byte shall not be necessary to prevent the DHCP option parser from running off the end of the buffer. */
    /* *DHCPOption++ = 0xFF; */
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, sizeof( DHCPMsg ) );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}

void test_vDHCPProcess_eWaitingAcknowledge_IncorrectDNSServerAddress( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 6U                                    /* DNS server */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, ulSubnetMask );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_GATEWAY_OPTION_CODE, ulGateway );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_LEASE_TIME_OPTION_CODE, ulLeaseTime );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_DNS_SERVER_OPTIONS_CODE, FREERTOS_INADDR_ANY );

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}

void test_vDHCPProcess_eWaitingAcknowledge_IncorrectDNSServerAddress2( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 6U                                    /* DNS server */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    uint32_t ulDNSServer = 0xC0010101;       /* 192.1.1.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    IPV4Parameters_t * xIPv4Addressing = &( pxEndPoint->ipv4_settings );

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, ulSubnetMask );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_GATEWAY_OPTION_CODE, ulGateway );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_LEASE_TIME_OPTION_CODE, ulLeaseTime );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_DNS_SERVER_OPTIONS_CODE, ipBROADCAST_IP_ADDRESS );

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( configTICK_RATE_HZ * ( FreeRTOS_ntohl( ulLeaseTime ) >> 1 ), pxEndPoint->xDHCPData.ulLeaseTime );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulGatewayAddress, ulGateway );
    TEST_ASSERT_EQUAL( xIPv4Addressing->ulNetMask, ulSubnetMask );
}

void test_vDHCPProcess_eWaitingAcknowledge_IPv4ServerIncorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 6U                                    /* Lease time */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    DHCPMsg[ xTotalLength - 1U ] = 0xFF;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 1;
    /* Add the offer byte. */
    DHCPOption[ 2 ] = dhcpMESSAGE_TYPE_ACK;

    DHCPOption += 4;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 4;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    DHCPOption += 6;
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 3;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &DHCPServerAddress, sizeof( DHCPServerAddress ) );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Ignore();

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( dhcpDEFAULT_LEASE_TIME, pxEndPoint->xDHCPData.ulLeaseTime );
}


void test_vDHCPProcess_eWaitingAcknowledge_SubnetMaskIncorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 5U                                    /* Subnet Mask, truncated */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress );
    prvWriteDHCPOption( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, &ulSubnetMask, 3 );

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Ignore();

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( dhcpDEFAULT_LEASE_TIME, pxEndPoint->xDHCPData.ulLeaseTime );
}

void test_vDHCPProcess_eWaitingAcknowledge_GatewayIncorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, ulSubnetMask );

    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_GATEWAY_OPTION_CODE;
    /* Add incorrect length. */
    DHCPOption[ 1 ] = 2;
    /* Add the offer byte. */
    memcpy( &DHCPOption[ 2 ], &ulGateway, sizeof( ulGateway ) );
    DHCPOption += 6;

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Ignore();

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( dhcpDEFAULT_LEASE_TIME, pxEndPoint->xDHCPData.ulLeaseTime );
}


void test_vDHCPProcess_eWaitingAcknowledge_LeaseTimeIncorrectLength( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 5U                                    /* Lease time, truncated */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, ulSubnetMask );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_GATEWAY_OPTION_CODE, ulGateway );
    prvWriteDHCPOption( &DHCPOption, dhcpIPv4_LEASE_TIME_OPTION_CODE, &ulLeaseTime, 3 );

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    /* Expect this function to be called since we now have
     * successfully acquired an IP address. */
    vIPNetworkUpCalls_Expect( &xEndPoint );

    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    /* Expect ARP to begin. */
    vARPSendGratuitous_Expect();

    /* Expect the timer to be reloaded. */
    vDHCP_RATimerReload_Ignore();

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* DHCP socket should be unallocated */
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    /* Make sure that this is not changed. */
    TEST_ASSERT_EQUAL( dhcpDEFAULT_LEASE_TIME, pxEndPoint->xDHCPData.ulLeaseTime );
}

void test_vDHCPProcess_eWaitingAcknowledge_LeaseTimeIncorrectLength2( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 1U /* Padding */
                                    + 3U                                    /* DHCP offer */
                                    + 6U                                    /* Server IP address */
                                    + 6U                                    /* Subnet Mask */
                                    + 6U                                    /* Gateway */
                                    + 5U                                    /* Lease time */
                                    + 1U /* End */;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Leave one byte for the padding. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) + 1 ];

    prvWriteDHCPOptionU8( &DHCPOption, dhcpIPv4_MESSAGE_TYPE_OPTION_CODE, dhcpMESSAGE_TYPE_ACK );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SERVER_IP_ADDRESS_OPTION_CODE, DHCPServerAddress + 0x1234 );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_SUBNET_MASK_OPTION_CODE, ulSubnetMask );
    prvWriteDHCPOptionU32( &DHCPOption, dhcpIPv4_GATEWAY_OPTION_CODE, ulGateway );
    prvWriteDHCPOption( &DHCPOption, dhcpIPv4_LEASE_TIME_OPTION_CODE, &ulLeaseTime, 3 );

    *DHCPOption++ = 0xFF;
    TEST_ASSERT_EQUAL( DHCPOption - DHCPMsg, xTotalLength );

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );
    /* Release the UDP buffer. */
    FreeRTOS_ReleaseUDPPayloadBuffer_Expect( DHCPMsg );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );
    /* Should now be using leased address. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eWaitingAcknowledge_IncorrectLengthOfPacket( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;

    /* Create a bit longer DHCP message but keep it empty. */
    const BaseType_t xTotalLength = sizeof( struct xDHCPMessage_IPv4 ) + 2U;
    uint8_t DHCPMsg[ xTotalLength ];
    uint32_t DHCPServerAddress = 0xC0A80001; /* 192.168.0.1 */
    uint32_t ulClientIPAddress = 0xC0A8000A; /* 192.168.0.10 */
    uint32_t ulSubnetMask = 0xFFFFF100;      /* 255.255.241.0 */
    uint32_t ulGateway = 0xC0A80001;         /* 192.168.0.1 */
    uint32_t ulLeaseTime = 0x00000096;       /* 150 seconds */
    DHCPMessage_IPv4_t * pxDHCPMessage = ( DHCPMessage_IPv4_t * ) DHCPMsg;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    DHCPMsg[ xTotalLength - 1U ] = 0xFF;


    /* Set the header - or at least the start of DHCP message. */
    memset( DHCPMsg, 0, sizeof( DHCPMsg ) );
    /* Copy the header here. */
    memcpy( DHCPMsg, DHCP_header, sizeof( DHCP_header ) );
    /* Make sure that the address matches. */
    memcpy( pxDHCPMessage->ucClientHardwareAddress, xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    memcpy( &( pxEndPoint->xMACAddress.ucBytes ), xDefault_MacAddress.ucBytes, sizeof( MACAddress_t ) );
    /* Add the expected cookie. */
    pxDHCPMessage->ulDHCPCookie = dhcpCOOKIE;

    /* Set the client IP address. */
    pxDHCPMessage->ulYourIPAddress_yiaddr = ulClientIPAddress;

    /* Get pointer to the end. */
    uint8_t * DHCPOption = &DHCPMsg[ sizeof( struct xDHCPMessage_IPv4 ) ];
    /* Add Message type code. */
    DHCPOption[ 0 ] = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    /* Add length. */
    DHCPOption[ 1 ] = 0;

    /* Put the information in global variables to be returned by
     * the FreeRTOS_recvrom. */
    ucGenericPtr = DHCPMsg;
    ulGenericLength = sizeof( DHCPMsg );

    /* This should remain unchanged. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eWaitingAcknowledge;
    pxEndPoint->xDHCPData.eExpectedState = eWaitingAcknowledge;
    /* Not Using broadcast. */
    pxEndPoint->xDHCPData.xUseBroadcast = pdFALSE;
    /* Set the transaction ID which will match. */
    pxEndPoint->xDHCPData.ulTransactionId = 0x01ABCDEF;
    /* Put correct address. */
    pxEndPoint->xDHCPData.ulDHCPServerAddress = DHCPServerAddress;
    /* Reset the lease time. */
    pxEndPoint->xDHCPData.ulLeaseTime = 0;
    /* Put some time values. */
    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    /* Make sure that we don't exceed the period - and thus, don't give up. */
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;

    /* Reset this value so that it can be verified later. */
    pxEndPoint->ipv4_settings.ulIPAddress = 0;

    /* Get a stub. */
    FreeRTOS_recvfrom_Stub( FreeRTOS_recvfrom_Generic );

    /* Make sure that there is no timeout. The expression is: xTaskGetTickCount() - pxEndPoint->xDHCPData.xDHCPTxTime ) > pxEndPoint->xDHCPData.xDHCPTxPeriod  */
    /* Return a value which makes the difference just equal to the period. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxTime + pxEndPoint->xDHCPData.xDHCPTxPeriod + 100 );
    /* Return time second time which can be verified. */
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );

    /* Get the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Send succeeds. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    /* DHCP socket should be allocated */
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint->xDHCPData.xDHCPSocket );
    /* Should still be stuck in waiting for ack state. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eGetLinkLayerAddress_Timeout_NoARPIPClash( void )
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eGetLinkLayerAddress;
    pxEndPoint->xDHCPData.eExpectedState = eGetLinkLayerAddress;

    xARPHadIPClash = pdFALSE;
    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;

    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxPeriod + pxEndPoint->xDHCPData.xDHCPTxTime + 100 );

    vIPNetworkUpCalls_Expect( &xEndPoint );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eGetLinkLayerAddress_Timeout_ARPIPClash( void ) /* prvPrepareLinkLayerIPLookUp + prvCloseDHCPSocket */
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eGetLinkLayerAddress;
    pxEndPoint->xDHCPData.eExpectedState = eGetLinkLayerAddress;
    /* This should be nullified. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;

    xARPHadIPClash = pdTRUE;

    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxPeriod + pxEndPoint->xDHCPData.xDHCPTxTime + 100 );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    /* Then expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    vARPSendGratuitous_Expect();

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
}

void test_vDHCPProcess_eGetLinkLayerAddress_Timeout_ARPIPClash_NoSocketInUse( void ) /* prvPrepareLinkLayerIPLookUp + prvCloseDHCPSocket */
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eGetLinkLayerAddress;
    pxEndPoint->xDHCPData.eExpectedState = eGetLinkLayerAddress;
    /* This should be nullified. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 0;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;

    xARPHadIPClash = pdTRUE;

    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxPeriod + pxEndPoint->xDHCPData.xDHCPTxTime + 100 );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    /* Then expect the socket to be closed. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    vARPSendGratuitous_Expect();

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eGetLinkLayerAddress_Timeout_ARPIPClash_TwoSocketsInUse( void ) /* prvPrepareLinkLayerIPLookUp + prvCloseDHCPSocket */
{
    struct xSOCKET xTestSocket;
    TickType_t xTimeValue = 1234;
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eGetLinkLayerAddress;
    pxEndPoint->xDHCPData.eExpectedState = eGetLinkLayerAddress;
    /* This should be nullified. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 2;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;

    xARPHadIPClash = pdTRUE;

    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxPeriod + pxEndPoint->xDHCPData.xDHCPTxTime + 100 );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    vARPSendGratuitous_Expect();

    vDHCPProcessEndPoint( pdFALSE, pdFALSE, pxEndPoint );

    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eGetLinkLayerAddress_NoTimeout( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    pxEndPoint->xDHCPData.xDHCPTxTime = 100;
    pxEndPoint->xDHCPData.xDHCPTxPeriod = 100;
    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eGetLinkLayerAddress;
    pxEndPoint->xDHCPData.eExpectedState = eGetLinkLayerAddress;
    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;
    xARPHadIPClash = pdTRUE;

    /* Make it so that there is no timeout. */
    xTaskGetTickCount_ExpectAndReturn( pxEndPoint->xDHCPData.xDHCPTxPeriod + pxEndPoint->xDHCPData.xDHCPTxTime );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    TEST_ASSERT_EQUAL( eGetLinkLayerAddress, pxEndPoint->xDHCPData.eDHCPState );
}


void test_vDHCPProcess_eLeasedAddress_EndPointDown( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;
    struct xSOCKET xTestSocket;

    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdFALSE );

    /* Expect the DHCP timer to be reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint, pdMS_TO_TICKS( 5000U ) );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* Still in this phase. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_eLeasedAddress_NetworkUp_SocketCreated_RNGPass_GNBfail( void )
{
    struct xSOCKET xTestSocket;
    BaseType_t xTimeValue = 300;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Socket is already created. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;

    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdTRUE );

    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdTRUE );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Return the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning NULL will mean the prvSendDHCPDiscover fail. */
    pxGetNetworkBufferWithDescriptor_ExpectAnyArgsAndReturn( NULL );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    /* Expect the timer to be set. */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* Need to send DHCP request. */
    TEST_ASSERT_EQUAL( eSendDHCPRequest, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
    TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

void test_vDHCPProcess_eLeasedAddress_NetworkUp_SocketCreated_RNGFail( void )
{
    struct xSOCKET xTestSocket;
    BaseType_t xTimeValue = 300;
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Socket is already created. */
    xDHCPv4Socket = &xTestSocket;
    xDHCPSocketUserCount = 1;
    pxEndPoint->xDHCPData.xDHCPSocket = &xTestSocket;

    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdTRUE );

    /* Make RNG fail. */
    xApplicationGetRandomNumber_ExpectAnyArgsAndReturn( pdFALSE );
    xTaskGetTickCount_ExpectAndReturn( xTimeValue );
    /* Return the hostname. */
    pcApplicationHostnameHook_ExpectAndReturn( pcHostName );
    /* Returning a proper network buffer. */
    pxGetNetworkBufferWithDescriptor_Stub( GetNetworkBuffer );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    /* Make the call to FreeRTOS_send succeed. */
    FreeRTOS_sendto_ExpectAnyArgsAndReturn( 1 );

    /* Expect the timer to be set. */
    vDHCP_RATimerReload_Expect( &xEndPoint, dhcpINITIAL_TIMER_PERIOD );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* Sent DHCP request - waiting ACK. */
    TEST_ASSERT_EQUAL( eWaitingAcknowledge, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( xTimeValue, pxEndPoint->xDHCPData.xDHCPTxTime );
    TEST_ASSERT_EQUAL( dhcpINITIAL_DHCP_TX_PERIOD, pxEndPoint->xDHCPData.xDHCPTxPeriod );
}

void test_vDHCPProcess_eLeasedAddress_NetworkUp_SocketNotCreated_RNGPass_GNBfail( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Socket not created. */
    xDHCPv4Socket = NULL;
    pxEndPoint->xDHCPData.xDHCPSocket = NULL;

    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eLeasedAddress;

    FreeRTOS_IsEndPointUp_IgnoreAndReturn( pdTRUE );

    /* Return invalid socket. */
    FreeRTOS_socket_ExpectAnyArgsAndReturn( FREERTOS_INVALID_SOCKET );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    xSocketValid_ExpectAnyArgsAndReturn( pdFALSE );

    vDHCPProcess( pdFALSE, pxEndPoint );

    /* Still here. */
    TEST_ASSERT_EQUAL( eLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint->xDHCPData.xDHCPSocket );
}

void test_vDHCPProcess_eNotUsingLeasedAddress( void )
{
    NetworkEndPoint_t xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Put the required state. */
    pxEndPoint->xDHCPData.eDHCPState = eNotUsingLeasedAddress;
    pxEndPoint->xDHCPData.eExpectedState = eNotUsingLeasedAddress;

    /* Expect the timer to be disabled. */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint, pdFALSE );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* Continue not using DHCP. */
    TEST_ASSERT_EQUAL( eNotUsingLeasedAddress, pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_IncorrectState( void )
{
    struct xNetworkEndPoint xEndPoint = { 0 }, * pxEndPoint = &xEndPoint;

    /* Put a non-existent state. */
    pxEndPoint->xDHCPData.eDHCPState = ( eNotUsingLeasedAddress << 1 );
    pxEndPoint->xDHCPData.eExpectedState = ( eNotUsingLeasedAddress << 1 );

    vDHCPProcessEndPoint( pdFALSE, pdTRUE, pxEndPoint );

    /* Continue not using DHCP. */
    TEST_ASSERT_EQUAL( ( eNotUsingLeasedAddress << 1 ), pxEndPoint->xDHCPData.eDHCPState );
}

void test_vDHCPProcess_ResetWithRNGSuccessSocketSuccess_TwoEndPoints( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint_1 = { 0 }, * pxEndPoint_1 = &xEndPoint_1;
    NetworkEndPoint_t xEndPoint_2 = { 0 }, * pxEndPoint_2 = &xEndPoint_2;

    /* Socket not created. */
    xDHCPv4Socket = NULL;
    pxEndPoint_1->xDHCPData.xDHCPSocket = NULL;
    pxEndPoint_2->xDHCPData.xDHCPSocket = NULL;

    /* Make random number generation pass. */
    xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint_1->xDHCPData.ulTransactionId ), pdTRUE );
    /* Return a valid socket. */
    FreeRTOS_socket_ExpectAndReturn( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP, &xTestSocket );

    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );
    xSocketValid_ExpectAnyArgsAndReturn( pdTRUE );

    /* Ignore the inputs to setting the socket options. */
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
    FreeRTOS_setsockopt_ExpectAnyArgsAndReturn( pdPASS );
    /* Make sure that binding passes. Return zero. */
    vSocketBind_ExpectAnyArgsAndReturn( 0 );
    /* See if the timer is reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint_1, dhcpINITIAL_TIMER_PERIOD );

    vDHCPProcess( pdTRUE, pxEndPoint_1 );

    TEST_ASSERT_EQUAL( 1, xDHCPSocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_1->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint_2->xDHCPData.xDHCPSocket );

    /* Make random number generation pass. */
    xApplicationGetRandomNumber_ExpectAndReturn( &( pxEndPoint_2->xDHCPData.ulTransactionId ), pdTRUE );

    /* See if the timer is reloaded. */
    vDHCP_RATimerReload_Expect( &xEndPoint_2, dhcpINITIAL_TIMER_PERIOD );

    vDHCPProcess( pdTRUE, pxEndPoint_2 );

    TEST_ASSERT_EQUAL( 2, xDHCPSocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_1->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_2->xDHCPData.xDHCPSocket );
}

void test_vDHCPStop( void )
{
    struct xSOCKET xTestSocket;
    NetworkEndPoint_t xEndPoint_1 = { 0 }, * pxEndPoint_1 = &xEndPoint_1;
    NetworkEndPoint_t xEndPoint_2 = { 0 }, * pxEndPoint_2 = &xEndPoint_2;
    NetworkEndPoint_t xEndPoint_3 = { 0 }, * pxEndPoint_3 = &xEndPoint_3;

    /* Socket is already created. */
    xDHCPv4Socket = &xTestSocket;

    /* 2 end-points opened the socket */
    xDHCPSocketUserCount = 2;
    pxEndPoint_1->xDHCPData.xDHCPSocket = FREERTOS_INVALID_SOCKET;
    pxEndPoint_2->xDHCPData.xDHCPSocket = &xTestSocket;
    pxEndPoint_3->xDHCPData.xDHCPSocket = &xTestSocket;

    /* Stop DHCP for end-point 1 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_1, pdFALSE );

    vDHCPStop( pxEndPoint_1 );

    TEST_ASSERT_EQUAL( 2, xDHCPSocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( FREERTOS_INVALID_SOCKET, pxEndPoint_1->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_2->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_3->xDHCPData.xDHCPSocket );

    /* Stop DHCP for end-point 2 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_2, pdFALSE );

    vDHCPStop( pxEndPoint_2 );

    TEST_ASSERT_EQUAL( 1, xDHCPSocketUserCount );
    TEST_ASSERT_EQUAL( &xTestSocket, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint_2->xDHCPData.xDHCPSocket );
    TEST_ASSERT_EQUAL( &xTestSocket, pxEndPoint_3->xDHCPData.xDHCPSocket );

    /* Stop DHCP for end-point 3 */
    vIPSetDHCP_RATimerEnableState_Expect( &xEndPoint_3, pdFALSE );

    /* Expect the socket to be closed. */
    vSocketClose_ExpectAndReturn( &xTestSocket, NULL );

    vDHCPStop( pxEndPoint_3 );

    TEST_ASSERT_EQUAL( 0, xDHCPSocketUserCount );
    TEST_ASSERT_EQUAL( NULL, xDHCPv4Socket );
    TEST_ASSERT_EQUAL( NULL, pxEndPoint_3->xDHCPData.xDHCPSocket );
}

/*
 * @brief Check static function , in case of malformed packet , where length byte is zero.
 */

void test_xProcessCheckOption_LengthByteZero( void )
{
    BaseType_t xResult;
    ProcessSet_t xSet;

    uint8_t ucUDPPayload[ 2 ];

    memset( &( ucUDPPayload ), 0, sizeof( ucUDPPayload ) );

    memset( &( xSet ), 0, sizeof( xSet ) );
    xSet.ulProcessed = 0U;
    xSet.ucOptionCode = dhcpIPv4_MESSAGE_TYPE_OPTION_CODE;
    xSet.pucByte = ucUDPPayload;
    xSet.uxIndex = 0;
    xSet.uxPayloadDataLength = sizeof( ucUDPPayload );

    xResult = xProcessCheckOption( &xSet );

    TEST_ASSERT_EQUAL( -1, xResult );
}
