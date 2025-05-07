/*
 * coreSNTP v1.3.1
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_sntp_serializer.c
 * @brief Implementation of the Serializer API of the coreSNTP library.
 */

/* Standard includes. */
#include <string.h>
#include <stdbool.h>
#include <assert.h>

/* Include API header. */
#include "core_sntp_serializer.h"

#include "core_sntp_config_defaults.h"

/**
 * @brief The version of SNTP supported by the coreSNTP library by complying
 * with the SNTPv4 specification defined in [RFC 4330](https://tools.ietf.org/html/rfc4330).
 */
#define SNTP_VERSION                        ( 4U )

/**
 * @brief The bit mask for the "Mode" information in the first byte of an SNTP packet.
 * The "Mode" field occupies bits 0-2 of the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_BITS_MASK                 ( 0x07U )

/**
 * @brief The value indicating a "client" in the "Mode" field of an SNTP packet.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_CLIENT                    ( 3U )

/**
 * @brief The value indicating a "server" in the "Mode" field of an SNTP packet.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_MODE_SERVER                    ( 4U )

/**
 * @brief The position of the least significant bit of the "Leap Indicator" field
 * in first byte of an SNTP packet. The "Leap Indicator" field occupies bits 6-7 of the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_LEAP_INDICATOR_LSB_POSITION    ( 6 )

/**
 * @brief Value of Stratum field in SNTP packet representing a Kiss-o'-Death message
 * from server.
 */
#define SNTP_KISS_OF_DEATH_STRATUM          ( 0U )

/**
 * @brief The position of least significant bit of the "Version" information
 * in the first byte of an SNTP packet. "Version" field occupies bits 3-5 of
 * the byte.
 * @note Refer to the [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4)
 * for more information.
 */
#define SNTP_VERSION_LSB_POSITION           ( 3 )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "DENY", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_DENY_UINT_VALUE            ( 0x44454e59U )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "RSTR", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_RSTR_UINT_VALUE            ( 0x52535452U )

/**
 * @brief The integer value of the Kiss-o'-Death ASCII code, "RATE", used
 * for comparison with data in an SNTP response.
 * @note Refer to [RFC 4330 Section 8](https://tools.ietf.org/html/rfc4330#section-8)
 * for more information.
 */
#define KOD_CODE_RATE_UINT_VALUE            ( 0x52415445U )

/**
 * @brief Macro to represent exactly half of the total number of seconds in an NTP era.
 * As 32 bits are used to represent the "seconds" part of an SNTP timestamp, the half of
 * the total range of seconds in an NTP era is 2^31 seconds, which represents ~68 years.
 *
 * @note This macro represents the edge case of calculating the client system clock-offset
 * relative to server time as the library ASSUMES that the client and server times are within
 * 2^31 seconds apart in duration. This is done to support calculating clock-offset for the
 * cases when server and client systems are in adjacent NTP eras, which can occur when NTP time
 * wraps around in 2036, and the relative NTP era presence of client and server times is
 * determined based on comparing first order difference values between all possible NTP era
 * configurations of the systems.
 */
#define CLOCK_OFFSET_MAX_TIME_DIFFERENCE    ( ( ( ( int64_t ) INT32_MAX + 1 ) * 1000 ) )

/**
 * @brief Macro to represent the total number of milliseconds that are represented in an
 * NTP era period. This macro represents a duration of ~136 years.
 *
 * @note Rationale for calculation: The "seconds" part of an NTP timestamp is represented in
 * unsigned 32 bit width, thus, the total range of seconds it represents is 2^32,
 * i.e. (UINT32_MAX + 1).
 */
#define TOTAL_MILLISECONDS_IN_NTP_ERA       ( ( ( int64_t ) UINT32_MAX + 1 ) * 1000 )

/**
 * @brief Structure representing an SNTP packet header.
 * For more information on SNTP packet format, refer to
 * [RFC 4330 Section 4](https://tools.ietf.org/html/rfc4330#section-4).
 *
 * @note This does not include extension fields for authentication data
 * for secure SNTP communication. Authentication data follows the
 * packet header represented by this structure.
 */
typedef struct SntpPacket
{
    /**
     * @brief Bits 6-7 leap indicator, bits 3-5 are version number, bits 0-2 are mode
     */
    uint8_t leapVersionMode;

    /**
     * @brief stratum
     */
    uint8_t stratum;

    /**
     * @brief poll interval
     */
    uint8_t poll;

    /**
     * @brief precision
     */
    uint8_t precision;

    /**
     * @brief root delay
     */
    uint32_t rootDelay;

    /**
     * @brief root dispersion
     */
    uint32_t rootDispersion;

    /**
     * @brief reference ID
     */
    uint32_t refId;

    /**
     * @brief reference time
     */
    SntpTimestamp_t refTime;

    /**
     * @brief origin timestamp
     */
    SntpTimestamp_t originTime;

    /**
     * @brief receive timestamp
     */
    SntpTimestamp_t receiveTime;

    /**
     * @brief transmit timestamp
     */
    SntpTimestamp_t transmitTime;
} SntpPacket_t;

/**
 * @brief Utility macro to fill 32-bit integer in word-sized
 * memory in network byte (or Big Endian) order.
 *
 * @param[out] pWordMemory Pointer to the word-sized memory in which
 * the 32-bit integer will be filled.
 * @param[in] data The 32-bit integer to fill in the @p wordMemory
 * in network byte order.
 *
 * @note This utility ensures that data is filled in memory
 * in expected network byte order, as an assignment operation
 * (like *pWordMemory = word) can cause undesired side-effect
 * of network-byte ordering getting reversed on Little Endian platforms.
 */
static void fillWordMemoryInNetworkOrder( uint32_t * pWordMemory,
                                          uint32_t data )
{
    uint8_t * pByteMemory = ( uint8_t * ) pWordMemory;

    assert( pWordMemory != NULL );

    pByteMemory[ 0 ] = ( uint8_t ) ( data >> 24 );
    pByteMemory[ 1 ] = ( uint8_t ) ( ( data >> 16 ) & 0x000000FFU );
    pByteMemory[ 2 ] = ( uint8_t ) ( ( data >> 8 ) & 0x000000FFU );
    pByteMemory[ 3 ] = ( uint8_t ) ( ( data ) & 0x000000FFU );
}

/**
 * @brief Utility macro to generate a 32-bit integer from memory containing
 * integer in network (or Big Endian) byte order.
 * @param[in] ptr Pointer to the memory containing 32-bit integer in network
 * byte order.
 *
 * @return The host representation of the 32-bit integer in the passed word
 * memory.
 */
static uint32_t readWordFromNetworkByteOrderMemory( const uint32_t * ptr )
{
    const uint8_t * pMemStartByte = ( const uint8_t * ) ptr;

    assert( ptr != NULL );

    return ( uint32_t ) ( ( ( ( uint32_t ) pMemStartByte[ 0 ] ) << 24 ) |
                          ( 0x00FF0000U & ( ( ( uint32_t ) pMemStartByte[ 1 ] ) << 16 ) ) |
                          ( 0x0000FF00U & ( ( ( uint32_t ) pMemStartByte[ 2 ] ) << 8 ) ) |
                          ( ( uint32_t ) pMemStartByte[ 3 ] ) );
}

/**
 * @brief Utility to return absolute (or positively signed) value of an signed
 * 64 bit integer.
 *
 * @param[in] value The integer to return the absolute value of.
 *
 * @return The absolute value of @p value.
 */
static int64_t absoluteOf( int64_t value )
{
    return ( value >= 0 ) ? value : ( ( int64_t ) 0 - value );
}

/**
 * @brief Utility to determine whether a timestamp represents a zero
 * timestamp value.
 *
 * @note This utility is used to determine whether a timestamp value is
 * invalid. According to the SNTPv4 specification, a zero timestamp value
 * is considered invalid.
 *
 * @param[in] pTime The timestamp whose value is to be inspected for
 * zero value.
 *
 * @return `true` if the timestamp is zero; otherwise `false`.
 */
static bool isZeroTimestamp( const SntpTimestamp_t * pTime )
{
    bool isSecondsZero = ( pTime->seconds == 0U ) ? true : false;
    bool isFractionsZero = ( pTime->fractions == 0U ) ? true : false;

    return( isSecondsZero && isFractionsZero );
}

/**
 * @brief Utility to convert the "fractions" part of an SNTP timestamp to milliseconds
 * duration of time.
 * @param[in] fractions The fractions value.
 *
 * @return The milliseconds equivalent of the @p fractions value.
 */
static uint32_t fractionsToMs( uint32_t fractions )
{
    return( fractions / ( 1000U * SNTP_FRACTION_VALUE_PER_MICROSECOND ) );
}

/**
 * @brief Utility to safely calculate difference between server and client timestamps and
 * return the difference in the resolution of milliseconds as a signed 64 bit integer.
 * The calculated value represents the effective subtraction as ( @p serverTimeSec - @p clientTimeSec ).
 *
 * @note This utility SUPPORTS the cases of server and client timestamps being in different NTP eras,
 * and ASSUMES that the server and client systems are within 68 years of each other.
 * To handle the case of different NTP eras, this function calculates difference values for all
 * possible combinations of NTP eras of server and client times (i.e. 1. both timestamps in same era,
 * 2. server timestamp one era ahead, and 3. client timestamp being one era ahead), and determines
 * the NTP era configuration by choosing the difference value of the smallest absolute value.
 *
 * @param[in] pServerTime The server timestamp.
 * @param[in] pClientTime The client timestamp.
 *
 * @return The calculated difference between server and client times as a signed 64 bit integer.
 */
static int64_t safeTimeDifference( const SntpTimestamp_t * pServerTime,
                                   const SntpTimestamp_t * pClientTime )
{
    int64_t eraAdjustedDiff = 0;

    /* Convert the timestamps into 64 bit signed integer values of milliseconds. */
    int64_t serverTime = ( ( int64_t ) pServerTime->seconds * 1000 ) + ( int64_t ) fractionsToMs( pServerTime->fractions );
    int64_t clientTime = ( ( int64_t ) pClientTime->seconds * 1000 ) + ( int64_t ) fractionsToMs( pClientTime->fractions );

    /* The difference between the 2 timestamps is calculated by determining the whether the timestamps
     * are present in the same NTP era or adjacent NTP eras (i.e. the NTP timestamp overflow case). */

    /* First, calculate the first order time difference assuming that server and client times
     * are in the same NTP era. */
    int64_t diffWithNoEraAdjustment = serverTime - clientTime;

    /* Store the absolute value of the time difference which will be used for comparison with
     * different cases of relative NTP era configuration of client and server times. */
    int64_t absSameEraDiff = absoluteOf( diffWithNoEraAdjustment );

    /* If the absolute difference value is 2^31 seconds, it means that the server and client times are
     * away by exactly half the range of SNTP timestamp "second" values representable in unsigned 32 bits.
     * In such a case, irrespective of whether the 2 systems exist in the same or adjacent NTP eras, the
     * time difference calculated between the systems will ALWAYS yield the same value when viewed from
     * all NTP era configurations of the times.
     * For such a case, we will ASSUME that the server time is AHEAD of client time, and thus, generate
     * a positive clock-offset value.
     */
    if( absSameEraDiff == CLOCK_OFFSET_MAX_TIME_DIFFERENCE )
    {
        /* It does not matter whether server and client are in the same era for this
         * special case as the difference value for both same and adjacent eras will yield
         * the same absolute value of 2^31.*/
        eraAdjustedDiff = CLOCK_OFFSET_MAX_TIME_DIFFERENCE;
    }
    else
    {
        /* Determine if server time belongs to an NTP era different than the client time, and accordingly
         * choose the 64 bit representation of the first order difference to account for the era.
         * The logic for determining the relative era presence of the timestamps is by calculating the
         * first order difference (of "Server Time - Client Time") for all the 3 different era combinations
         * (1. both timestamps in same era, 2. server time one era ahead, 3. client time one era ahead)
         * and choosing the NTP era configuration that has the smallest first order difference value.
         */
        int64_t diffWithServerEraAdjustment = serverTime + TOTAL_MILLISECONDS_IN_NTP_ERA -
                                              clientTime;                                     /* This helps determine whether server is an
                                                                                               * era ahead of client time. */
        int64_t diffWithClientEraAdjustment = serverTime -
                                              ( TOTAL_MILLISECONDS_IN_NTP_ERA + clientTime ); /* This helps determine whether server is an
                                                                                               * era behind of client time. */

        /* Store the absolute value equivalents of all the time difference configurations
         * for easier comparison to smallest value from them. */
        int64_t absServerEraAheadDiff = absoluteOf( diffWithServerEraAdjustment );
        int64_t absClientEraAheadDiff = absoluteOf( diffWithClientEraAdjustment );

        /* Determine the correct relative era of client and server times by checking which era
         * configuration of difference value represents the least difference. */
        if( ( absSameEraDiff <= absServerEraAheadDiff ) && ( absSameEraDiff <= absClientEraAheadDiff ) )
        {
            /* Both server and client times are in the same era. */
            eraAdjustedDiff = diffWithNoEraAdjustment;
        }
        /* Check if server time is an NTP era ahead of client time. */
        else if( absServerEraAheadDiff < absSameEraDiff )
        {
            /* Server time is in NTP era 1 while client time is in NTP era 0. */
            eraAdjustedDiff = diffWithServerEraAdjustment;
        }
        /* Now, we know that the client time is an era ahead of server time. */
        else
        {
            /* Server time is in NTP era 0 while client time is in NTP era 1. */
            eraAdjustedDiff = diffWithClientEraAdjustment;
        }
    }

    return eraAdjustedDiff;
}

/**
 * @brief Utility to calculate clock offset of system relative to the
 * server using the on-wire protocol specified in the NTPv4 specification.
 * For more information on on-wire protocol, refer to
 * [RFC 5905 Section 8](https://tools.ietf.org/html/rfc5905#section-8).
 *
 * @note The following diagram explains the calculation of the clock
 * offset:
 *
 *                 T2      T3
 *      ---------------------------------   <-----   *SNTP/NTP server*
 *               /\         \
 *               /           \
 *     Request* /             \ *Response*
 *             /              \/
 *      ---------------------------------   <-----   *SNTP client*
 *           T1                T4
 *
 *  The four most recent timestamps, T1 through T4, are used to compute
 *  the clock offset of SNTP client relative to the server where:
 *
 *     T1 = Client Request Transmit Time
 *     T2 = Server Receive Time (of client request)
 *     T3 = Server Response Transmit Time
 *     T4 = Client Receive Time (of server response)
 *
 *  Clock Offset = T(NTP/SNTP server) - T(SNTP client)
 *               = [( T2 - T1 ) + ( T3 - T4 )]
 *                 ---------------------------
 *                              2
 *
 * @note Both NTPv4 and SNTPv4 specifications suggest calculating the
 * clock offset value, if possible. As the timestamp format uses 64 bit
 * integer and there exist 2 orders of arithmetic calculations on the
 * timestamp values (subtraction followed by addition as shown in the
 * diagram above), the clock offset for the system can be calculated
 * ONLY if the value can be represented in 62 significant bits and 2 sign
 * bits i.e. if the system clock is within 34 years (in the future or past)
 * of the server time.
 *
 * @param[in] pClientTxTime The system time of sending the SNTP request.
 * This is the same as "T1" in the above diagram.
 * @param[in] pServerRxTime The server time of receiving the SNTP request
 * packet from the client. This is the same as "T2" in the above diagram.
 * @param[in] pServerTxTime The server time of sending the SNTP response
 * packet. This is the same as "T3" in the above diagram.
 * @param[in] pClientRxTime The system time of receiving the SNTP response
 * from the server. This is the same as "T4" in the above diagram.
 * @param[out] pClockOffset This will be filled with the calculated offset value
 * of the system clock relative to the server time with the assumption that the
 * system clock is within 68 years of server time.
 */
static void calculateClockOffset( const SntpTimestamp_t * pClientTxTime,
                                  const SntpTimestamp_t * pServerRxTime,
                                  const SntpTimestamp_t * pServerTxTime,
                                  const SntpTimestamp_t * pClientRxTime,
                                  int64_t * pClockOffset )
{
    /* Variable for storing the first-order difference between timestamps. */
    int64_t firstOrderDiffSend = 0;
    int64_t firstOrderDiffRecv = 0;

    assert( pClientTxTime != NULL );
    assert( pServerRxTime != NULL );
    assert( pServerTxTime != NULL );
    assert( pClientRxTime != NULL );
    assert( pClockOffset != NULL );

    /* Perform first order difference of timestamps on the network send path i.e. T2 - T1.
     * Note: The calculated difference value will always represent years in the range of
     *[-68 years, +68 years]. */
    firstOrderDiffSend = safeTimeDifference( pServerRxTime, pClientTxTime );

    /* Perform first order difference of timestamps on the network receive path i.e. T3 - T4.
     * Note: The calculated difference value will always represent years in the range of
     *[-68 years, +68 years]. */
    firstOrderDiffRecv = safeTimeDifference( pServerTxTime, pClientRxTime );

    /* Now calculate the system clock-offset relative to server time as the average of the
     * first order difference of timestamps in both directions of network path.
     * Note: This will ALWAYS represent offset in the range of [-68 years, +68 years]. */
    *pClockOffset = ( firstOrderDiffSend + firstOrderDiffRecv ) / 2;
}

/**
 * @brief Parse a SNTP response packet by determining whether it is a rejected
 * or accepted response to an SNTP request, and accordingly, populate the
 * @p pParsedResponse parameter with the parsed data.
 *
 * @note If the server has rejected the request with the a Kiss-o'-Death message,
 * then this function will set the associated rejection code in the output parameter
 * while setting the remaining members to zero.
 * If the server has accepted the time request, then the function will set the
 * rejectedResponseCode member of the output parameter to #SNTP_KISS_OF_DEATH_CODE_NONE,
 * and set the other the members with appropriate data extracted from the response
 * packet.
 *
 * @param[in] pResponsePacket The SNTP response packet from server to parse.
 * @param[in] pRequestTxTime The system time (in SNTP timestamp format) of
 * sending the SNTP request to server.
 * @param[in] pResponseRxTime The system time (in SNTP timestamp format) of
 * receiving the SNTP response from server.
 * @param[out] pParsedResponse The parameter that will be populated with data
 * parsed from the response packet, @p pResponsePacket.
 *
 * @return This function returns one of the following:
 * - #SntpSuccess if the server response does not represent a Kiss-o'-Death
 * message.
 * - #SntpRejectedResponseChangeServer if the server rejected with a code
 * indicating that client cannot be retry requests to it.
 * - #SntpRejectedResponseRetryWithBackoff if the server rejected with a code
 * indicating that client should back-off before retrying request.
 * - #SntpRejectedResponseOtherCode if the server rejected with a code
 * other than "DENY", "RSTR" and "RATE".
 */
static SntpStatus_t parseValidSntpResponse( const SntpPacket_t * pResponsePacket,
                                            const SntpTimestamp_t * pRequestTxTime,
                                            const SntpTimestamp_t * pResponseRxTime,
                                            SntpResponseData_t * pParsedResponse )
{
    SntpStatus_t status = SntpSuccess;

    assert( pResponsePacket != NULL );
    assert( pResponseRxTime != NULL );
    assert( pParsedResponse != NULL );

    /* Clear the output parameter memory to zero. */
    ( void ) memset( pParsedResponse, 0, sizeof( *pParsedResponse ) );

    /* Determine if the server has accepted or rejected the request for time. */
    if( pResponsePacket->stratum == SNTP_KISS_OF_DEATH_STRATUM )
    {
        /* Server has sent a Kiss-o'-Death message i.e. rejected the request. */

        /* Extract the kiss-code sent by the server from the "Reference ID" field
         * of the SNTP packet. */
        pParsedResponse->rejectedResponseCode =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->refId );

        /* Determine the return code based on the Kiss-o'-Death code. */
        switch( pParsedResponse->rejectedResponseCode )
        {
            case KOD_CODE_DENY_UINT_VALUE:
            case KOD_CODE_RSTR_UINT_VALUE:
                status = SntpRejectedResponseChangeServer;
                break;

            case KOD_CODE_RATE_UINT_VALUE:
                status = SntpRejectedResponseRetryWithBackoff;
                break;

            default:
                status = SntpRejectedResponseOtherCode;
                break;
        }
    }
    else
    {
        /* Server has responded successfully to the time request. */

        SntpTimestamp_t serverRxTime;

        /* Map of integer value to SntpLeapSecondInfo_t enumeration type for the
         * "Leap Indicator" field in the first byte of an SNTP packet.
         * Note: This map is used to not violate MISRA Rule 10.5 when directly
         * converting an integer to enumeration type.
         */
        const SntpLeapSecondInfo_t leapIndicatorTypeMap[] =
        {
            NoLeapSecond,
            LastMinuteHas61Seconds,
            LastMinuteHas59Seconds,
            AlarmServerNotSynchronized
        };

        /* Set the Kiss-o'-Death code value to NULL as server has responded favorably
         * to the time request. */
        pParsedResponse->rejectedResponseCode = SNTP_KISS_OF_DEATH_CODE_NONE;

        /* Fill the output parameter with the server time which is the
         * "transmit" time in the response packet. */
        pParsedResponse->serverTime.seconds =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->transmitTime.seconds );
        pParsedResponse->serverTime.fractions =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->transmitTime.fractions );

        /* Extract information of any upcoming leap second from the response. */
        pParsedResponse->leapSecondType = leapIndicatorTypeMap[
            ( pResponsePacket->leapVersionMode >> SNTP_LEAP_INDICATOR_LSB_POSITION ) ];

        /* Store the "receive" time in SNTP response packet in host order. */
        serverRxTime.seconds =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->receiveTime.seconds );
        serverRxTime.fractions =
            readWordFromNetworkByteOrderMemory( &pResponsePacket->receiveTime.fractions );

        /* Calculate system clock offset relative to server time, if possible, within
         * the 64 bit integer width of the SNTP timestamp. */
        calculateClockOffset( pRequestTxTime,
                              &serverRxTime,
                              &pParsedResponse->serverTime,
                              pResponseRxTime,
                              &pParsedResponse->clockOffsetMs );
    }

    return status;
}


SntpStatus_t Sntp_SerializeRequest( SntpTimestamp_t * pRequestTime,
                                    uint32_t randomNumber,
                                    void * pBuffer,
                                    size_t bufferSize )
{
    SntpStatus_t status = SntpSuccess;

    if( pRequestTime == NULL )
    {
        status = SntpErrorBadParameter;
    }
    else if( pBuffer == NULL )
    {
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        status = SntpErrorBufferTooSmall;
    }

    /* Zero timestamps for client request time is not allowed to protect against
     * attack spoofing server response containing zero value for "originate timestamp".
     * Note: In SNTP/NTP communication, the "originate timestamp" of a valid server response
     * matches the "transmit timestamp" in corresponding client request packet. */
    else if( isZeroTimestamp( pRequestTime ) == true )
    {
        status = SntpErrorBadParameter;
    }
    else
    {
        /* MISRA Ref 11.5.1 [Void pointer assignment] */
        /* More details at: https://github.com/FreeRTOS/coreSNTP/blob/main/MISRA.md#rule-115 */
        /* coverity[misra_c_2012_rule_11_5_violation] */
        SntpPacket_t * pRequestPacket = ( SntpPacket_t * ) pBuffer;

        /* Fill the buffer with zero as most fields are zero for a standard SNTP
         * request packet.*/
        ( void ) memset( pBuffer, 0, sizeof( SntpPacket_t ) );

        /* Set the first byte of the request packet for "Version" and "Mode" fields */
        pRequestPacket->leapVersionMode = 0U /* Leap Indicator */ |
                                          ( SNTP_VERSION << SNTP_VERSION_LSB_POSITION ) /* Version Number */ |
                                          SNTP_MODE_CLIENT /* Mode */;


        /* Add passed random number to non-significant bits of the fractions part
         * of the transmit timestamp.
         * This is suggested by the SNTPv4 (and NTPv4) specification(s)
         * to protect against replay attacks. Refer to RFC 4330 Section 3 for
         * more information.
         * Adding random bits to the least significant 16 bits of the fractions
         * part of the timestamp affects only ~15 microseconds of information
         * (calculated as 0xFFFF * 232 picoseconds).
         */
        pRequestTime->fractions = ( pRequestTime->fractions
                                    | ( randomNumber >> 16 ) );

        /* Update the request buffer with request timestamp in network byte order. */
        fillWordMemoryInNetworkOrder( &pRequestPacket->transmitTime.seconds,
                                      pRequestTime->seconds );
        fillWordMemoryInNetworkOrder( &pRequestPacket->transmitTime.fractions,
                                      pRequestTime->fractions );
    }

    return status;
}


SntpStatus_t Sntp_DeserializeResponse( const SntpTimestamp_t * pRequestTime,
                                       const SntpTimestamp_t * pResponseRxTime,
                                       const void * pResponseBuffer,
                                       size_t bufferSize,
                                       SntpResponseData_t * pParsedResponse )
{
    SntpStatus_t status = SntpSuccess;
    /* MISRA Ref 11.5.1 [Void pointer assignment] */
    /* More details at: https://github.com/FreeRTOS/coreSNTP/blob/main/MISRA.md#rule-115 */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    const SntpPacket_t * pResponsePacket = ( const SntpPacket_t * ) pResponseBuffer;

    if( ( pRequestTime == NULL ) || ( pResponseRxTime == NULL ) ||
        ( pResponseBuffer == NULL ) || ( pParsedResponse == NULL ) )
    {
        status = SntpErrorBadParameter;
    }
    else if( bufferSize < SNTP_PACKET_BASE_SIZE )
    {
        status = SntpErrorBufferTooSmall;
    }

    /* Zero timestamps for client request time is not allowed to protect against
     * attack spoofing server response containing zero value for "originate timestamp".
     * Note: In SNTP/NTP communication, the "originate timestamp" of a valid server response
     * matches the "transmit timestamp" in corresponding client request packet. */
    else if( isZeroTimestamp( pRequestTime ) == true )
    {
        status = SntpErrorBadParameter;
    }
    /* Check if the packet represents a server in the "Mode" field. */
    else if( ( pResponsePacket->leapVersionMode & SNTP_MODE_BITS_MASK ) != SNTP_MODE_SERVER )
    {
        status = SntpInvalidResponse;
    }

    /* Check if any of the timestamps in the response packet are zero, which is invalid.
     * Note: This is done to protect against a nuanced server spoofing attack where if the
     * SNTP client resets its internal state of "Client transmit timestamp" (OR "originate
     * timestamp" from server perspective) to zero as a protection against replay attack, an
     * an attacker with this knowledge of the client operation can spoof a server response
     * containing the "originate timestamp" as zero. Thus, to protect against such attack,
     * a server response packet with any zero timestamp is rejected. */
    else if( ( isZeroTimestamp( &pResponsePacket->originTime ) == true ) ||
             ( isZeroTimestamp( &pResponsePacket->receiveTime ) == true ) ||
             ( isZeroTimestamp( &pResponsePacket->transmitTime ) == true ) )
    {
        status = SntpInvalidResponse;
    }


    /* Validate that the server has sent the client's request timestamp in the
     * "originate" timestamp field of the response. */
    else if( ( pRequestTime->seconds !=
               readWordFromNetworkByteOrderMemory( &pResponsePacket->originTime.seconds ) ) ||
             ( pRequestTime->fractions !=
               readWordFromNetworkByteOrderMemory( &pResponsePacket->originTime.fractions ) ) )

    {
        status = SntpInvalidResponse;
    }
    else
    {
        /* As the response packet is valid, parse more information from it and
         * populate the output parameter. */

        status = parseValidSntpResponse( pResponsePacket,
                                         pRequestTime,
                                         pResponseRxTime,
                                         pParsedResponse );
    }

    return status;
}

SntpStatus_t Sntp_CalculatePollInterval( uint16_t clockFreqTolerance,
                                         uint16_t desiredAccuracy,
                                         uint32_t * pPollInterval )
{
    SntpStatus_t status = SntpSuccess;

    if( ( clockFreqTolerance == 0U ) || ( desiredAccuracy == 0U ) || ( pPollInterval == NULL ) )
    {
        status = SntpErrorBadParameter;
    }
    else
    {
        uint32_t exactIntervalForAccuracy = 0U;
        uint8_t log2PollInterval = 0U;

        /* Calculate the poll interval required for achieving the exact desired clock accuracy
         * with the following formulae:
         *
         * System Clock Drift Rate ( microseconds / second ) = Clock Frequency Tolerance (in PPM )
         * Maximum Clock Drift ( milliseconds ) = Desired Accuracy ( milliseconds )
         *
         * Poll Interval ( seconds ) =     Maximum Clock Drift
         *                              ---------------------------
         *                                System Clock Drift Rate
         *
         *                           =  Maximum Drift ( milliseconds ) * 1000 ( microseconds / millisecond )
         *                             ------------------------------------------------------------------------
         *                                        System Clock Drift Rate ( microseconds / second )
         *
         *                           =    Desired Accuracy * 1000
         *                             ------------------------------
         *                               Clock Frequency Tolerance
         */
        exactIntervalForAccuracy = ( ( uint32_t ) desiredAccuracy * 1000U ) / clockFreqTolerance;

        /* Check if calculated poll interval value falls in the supported range of seconds. */
        if( exactIntervalForAccuracy == 0U )
        {
            /* Poll interval value is less than 1 second, and is not supported by the function. */
            status = SntpZeroPollInterval;
        }
        else
        {
            /* To calculate the log 2 value of the exact poll interval value, first determine the highest
             * bit set in the value. */
            while( exactIntervalForAccuracy != 0U )
            {
                log2PollInterval++;
                exactIntervalForAccuracy /= 2U;
            }

            /* Convert the highest bit in the exact poll interval value to the nearest integer
             * value lower or equal to the log2 of the exact poll interval value. */
            log2PollInterval--;

            /* Calculate the poll interval as the closest exponent of 2 value that achieves
             * equal or higher accuracy than the desired accuracy. */
            *pPollInterval = ( ( ( uint32_t ) 1U ) << log2PollInterval );
        }
    }

    return status;
}

SntpStatus_t Sntp_ConvertToUnixTime( const SntpTimestamp_t * pSntpTime,
                                     uint32_t * pUnixTimeSecs,
                                     uint32_t * pUnixTimeMicrosecs )
{
    SntpStatus_t status = SntpSuccess;

    if( ( pSntpTime == NULL ) || ( pUnixTimeSecs == NULL ) || ( pUnixTimeMicrosecs == NULL ) )
    {
        status = SntpErrorBadParameter;
    }
    /* Check if passed time does not lie in the [UNIX epoch in 1970, UNIX time overflow in 2038] time range. */
    else if( ( pSntpTime->seconds > SNTP_TIME_AT_LARGEST_UNIX_TIME_SECS ) &&
             ( pSntpTime->seconds < SNTP_TIME_AT_UNIX_EPOCH_SECS ) )
    {
        /* The SNTP timestamp is outside the supported time range for conversion. */
        status = SntpErrorTimeNotSupported;
    }
    else
    {
        /* Handle case when timestamp represents date in SNTP era 1
         * (i.e. time from 7 Feb 2036 6:28:16 UTC onwards). */
        if( pSntpTime->seconds <= SNTP_TIME_AT_LARGEST_UNIX_TIME_SECS )
        {
            /* Unix Time ( seconds ) = Seconds Duration in
             *                         [UNIX epoch, SNTP Era 1 Epoch Time]
             *                                        +
             *                           Sntp Time since Era 1 Epoch
             */
            *pUnixTimeSecs = UNIX_TIME_SECS_AT_SNTP_ERA_1_SMALLEST_TIME + pSntpTime->seconds;
        }
        /* Handle case when SNTP timestamp is in SNTP era 1 time range. */
        else
        {
            *pUnixTimeSecs = pSntpTime->seconds - SNTP_TIME_AT_UNIX_EPOCH_SECS;
        }

        /* Convert SNTP fractions to microseconds for UNIX time. */
        *pUnixTimeMicrosecs = pSntpTime->fractions / SNTP_FRACTION_VALUE_PER_MICROSECOND;
    }

    return status;
}
