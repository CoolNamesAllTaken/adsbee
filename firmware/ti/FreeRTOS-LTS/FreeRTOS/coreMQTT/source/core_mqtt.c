/*
 * coreMQTT v2.3.1
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_mqtt.c
 * @brief Implements the user-facing functions in core_mqtt.h.
 */
#include <string.h>
#include <assert.h>

#include "core_mqtt.h"
#include "core_mqtt_state.h"

/* Include config defaults header to get default values of configs. */
#include "core_mqtt_config_defaults.h"

#ifndef MQTT_PRE_SEND_HOOK

/**
 * @brief Hook called before a 'send' operation is executed.
 */
    #define MQTT_PRE_SEND_HOOK( pContext )
#endif /* !MQTT_PRE_SEND_HOOK */

#ifndef MQTT_POST_SEND_HOOK

/**
 * @brief Hook called after the 'send' operation is complete.
 */
    #define MQTT_POST_SEND_HOOK( pContext )
#endif /* !MQTT_POST_SEND_HOOK */

#ifndef MQTT_PRE_STATE_UPDATE_HOOK

/**
 * @brief Hook called just before an update to the MQTT state is made.
 */
    #define MQTT_PRE_STATE_UPDATE_HOOK( pContext )
#endif /* !MQTT_PRE_STATE_UPDATE_HOOK */

#ifndef MQTT_POST_STATE_UPDATE_HOOK

/**
 * @brief Hook called just after an update to the MQTT state has
 * been made.
 */
    #define MQTT_POST_STATE_UPDATE_HOOK( pContext )
#endif /* !MQTT_POST_STATE_UPDATE_HOOK */

/**
 * @brief Bytes required to encode any string length in an MQTT packet header.
 * Length is always encoded in two bytes according to the MQTT specification.
 */
#define CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES          ( 2U )

/**
 * @brief Number of vectors required to encode one topic filter in a subscribe
 * request. Three vectors are required as there are three fields in the
 * subscribe request namely:
 * 1. Topic filter length; 2. Topic filter; and 3. QoS in this order.
 */
#define CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH      ( 3U )

/**
 * @brief Number of vectors required to encode one topic filter in an
 * unsubscribe request. Two vectors are required as there are two fields in the
 * unsubscribe request namely:
 * 1. Topic filter length; and 2. Topic filter in this order.
 */
#define CORE_MQTT_UNSUBSCRIBE_PER_TOPIC_VECTOR_LENGTH    ( 2U )

/*-----------------------------------------------------------*/

/**
 * @brief Sends provided buffer to network using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pBufferToSend Buffer to be sent to network.
 * @brief param[in] bytesToSend Number of bytes to be sent.
 *
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a bytesToSend have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return Total number of bytes sent, or negative value on network error.
 */
static int32_t sendBuffer( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );

/**
 * @brief Sends MQTT connect without copying the users data into any buffer.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pConnectInfo MQTT CONNECT packet information.
 * @brief param[in] pWillInfo Last Will and Testament. Pass NULL if Last Will and
 * Testament is not used.
 * @brief param[in] remainingLength the length of the connect packet.
 *
 * @note This operation may call the transport send function
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes @a remainingLength have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return #MQTTSendFailed or #MQTTSuccess.
 */
static MQTTStatus_t sendConnectWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTConnectInfo_t * pConnectInfo,
                                            const MQTTPublishInfo_t * pWillInfo,
                                            size_t remainingLength );

/**
 * @brief Sends the vector array passed through the parameters over the network.
 *
 * @note The preference is given to 'writev' function if it is present in the
 * transport interface. Otherwise, a send call is made repeatedly to achieve the
 * result.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pIoVec The vector array to be sent.
 * @param[in] ioVecCount The number of elements in the array.
 *
 * @note This operation may call the transport send or writev functions
 * repeatedly to send bytes over the network until either:
 * 1. The requested number of bytes have been sent.
 *                    OR
 * 2. MQTT_SEND_TIMEOUT_MS milliseconds have gone by since entering this
 * function.
 *                    OR
 * 3. There is an error in sending data over the network.
 *
 * @return The total number of bytes sent or the error code as received from the
 * transport interface.
 */
static int32_t sendMessageVector( MQTTContext_t * pContext,
                                  TransportOutVector_t * pIoVec,
                                  size_t ioVecCount );

/**
 * @brief Add a string and its length after serializing it in a manner outlined by
 * the MQTT specification.
 *
 * @param[in] serializedLength Array of two bytes to which the vector will point.
 * The array must remain in scope until the message has been sent.
 * @param[in] string The string to be serialized.
 * @param[in] length The length of the string to be serialized.
 * @param[in] iterator The iterator pointing to the first element in the
 * transport interface IO array.
 * @param[out] updatedLength This parameter will be added to with the number of
 * bytes added to the vector.
 *
 * @return The number of vectors added.
 */
static size_t addEncodedStringToVector( uint8_t serializedLength[ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ],
                                        const char * const string,
                                        uint16_t length,
                                        TransportOutVector_t * iterator,
                                        size_t * updatedLength );

/**
 * @brief Send MQTT SUBSCRIBE message without copying the user data into a buffer and
 * directly sending it.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The count of elements in the list.
 * @param[in] packetId The packet ID of the subscribe packet
 * @param[in] remainingLength The remaining length of the subscribe packet.
 *
 * @return #MQTTSuccess or #MQTTSendFailed.
 */
static MQTTStatus_t sendSubscribeWithoutCopy( MQTTContext_t * pContext,
                                              const MQTTSubscribeInfo_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint16_t packetId,
                                              size_t remainingLength );

/**
 * @brief Send MQTT UNSUBSCRIBE message without copying the user data into a buffer and
 * directly sending it.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList MQTT subscription info.
 * @param[in] subscriptionCount The count of elements in the list.
 * @param[in] packetId The packet ID of the unsubscribe packet.
 * @param[in] remainingLength The remaining length of the unsubscribe packet.
 *
 * @return #MQTTSuccess or #MQTTSendFailed.
 */
static MQTTStatus_t sendUnsubscribeWithoutCopy( MQTTContext_t * pContext,
                                                const MQTTSubscribeInfo_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint16_t packetId,
                                                size_t remainingLength );

/**
 * @brief Calculate the interval between two millisecond timestamps, including
 * when the later value has overflowed.
 *
 * @note In C, the operands are promoted to signed integers in subtraction.
 * Using this function avoids the need to cast the result of subtractions back
 * to uint32_t.
 *
 * @param[in] later The later time stamp, in milliseconds.
 * @param[in] start The earlier time stamp, in milliseconds.
 *
 * @return later - start.
 */
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );

/**
 * @brief Convert a byte indicating a publish ack type to an #MQTTPubAckType_t.
 *
 * @param[in] packetType First byte of fixed header.
 *
 * @return Type of ack.
 */
static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType );

/**
 * @brief Receive bytes into the network buffer.
 *
 * @param[in] pContext Initialized MQTT Context.
 * @param[in] bytesToRecv Number of bytes to receive.
 *
 * @note This operation calls the transport receive function
 * repeatedly to read bytes from the network until either:
 * 1. The requested number of bytes @a bytesToRecv are read.
 *                    OR
 * 2. No data is received from the network for MQTT_RECV_POLLING_TIMEOUT_MS duration.
 *
 *                    OR
 * 3. There is an error in reading from the network.
 *
 *
 * @return Number of bytes received, or negative number on network error.
 */
static int32_t recvExact( const MQTTContext_t * pContext,
                          size_t bytesToRecv );

/**
 * @brief Discard a packet from the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] remainingLength Remaining length of the packet to dump.
 * @param[in] timeoutMs Time remaining to discard the packet.
 *
 * @return #MQTTRecvFailed or #MQTTNoDataAvailable.
 */
static MQTTStatus_t discardPacket( const MQTTContext_t * pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs );

/**
 * @brief Discard a packet from the MQTT buffer and the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pPacketInfo Information struct of the packet to be discarded.
 *
 * @return #MQTTRecvFailed or #MQTTNoDataAvailable.
 */
static MQTTStatus_t discardStoredPacket( MQTTContext_t * pContext,
                                         const MQTTPacketInfo_t * pPacketInfo );

/**
 * @brief Receive a packet from the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] incomingPacket packet struct with remaining length.
 * @param[in] remainingTimeMs Time remaining to receive the packet.
 *
 * @return #MQTTSuccess or #MQTTRecvFailed.
 */
static MQTTStatus_t receivePacket( const MQTTContext_t * pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs );

/**
 * @brief Get the correct ack type to send.
 *
 * @param[in] state Current state of publish.
 *
 * @return Packet Type byte of PUBACK, PUBREC, PUBREL, or PUBCOMP if one of
 * those should be sent, else 0.
 */
static uint8_t getAckTypeToSend( MQTTPublishState_t state );

/**
 * @brief Send acks for received QoS 1/2 publishes.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId packet ID of original PUBLISH.
 * @param[in] publishState Current publish state in record.
 *
 * @return #MQTTSuccess, #MQTTIllegalState or #MQTTSendFailed.
 */
static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState );

/**
 * @brief Send a keep alive PINGREQ if the keep alive interval has elapsed.
 *
 * @param[in] pContext Initialized MQTT Context.
 *
 * @return #MQTTKeepAliveTimeout if a PINGRESP is not received in time,
 * #MQTTSendFailed if the PINGREQ cannot be sent, or #MQTTSuccess.
 */
static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext );

/**
 * @brief Handle received MQTT PUBLISH packet.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState or deserialization error.
 */
static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT publish acks.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket );

/**
 * @brief Handle received MQTT ack.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 * @param[in] manageKeepAlive Flag indicating if PINGRESPs should not be given
 * to the application
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive );

/**
 * @brief Run a single iteration of the receive loop.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] manageKeepAlive Flag indicating if keep alive should be handled.
 *
 * @return #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * #MQTT_PINGRESP_TIMEOUT_MS milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            bool manageKeepAlive );

/**
 * @brief Validates parameters of #MQTT_Subscribe or #MQTT_Unsubscribe.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId );

/**
 * @brief Receives a CONNACK MQTT packet.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] timeoutMs Timeout for waiting for CONNACK packet.
 * @param[in] cleanSession Clean session flag set by application.
 * @param[out] pIncomingPacket List of MQTT subscription info.
 * @param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTBadResponse if a bad response is received;
 * #MQTTNoDataAvailable if no data available for transport recv;
 * ##MQTTRecvFailed if transport recv failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t receiveConnack( const MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent );

/**
 * @brief Resends pending acks for a re-established MQTT session, or
 * clears existing state records for a clean session.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] sessionPresent Session present flag received from the MQTT broker.
 *
 * @return #MQTTSendFailed if transport send during resend failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t handleSessionResumption( MQTTContext_t * pContext,
                                             bool sessionPresent );


/**
 * @brief Send the publish packet without copying the topic string and payload in
 * the buffer.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] pMqttHeader the serialized MQTT header with the header byte;
 * the encoded length of the packet; and the encoded length of the topic string.
 * @brief param[in] headerSize Size of the serialized PUBLISH header.
 * @brief param[in] packetId Packet Id of the publish packet.
 *
 * @return #MQTTSendFailed if transport send during resend failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t sendPublishWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTPublishInfo_t * pPublishInfo,
                                            const uint8_t * pMqttHeader,
                                            size_t headerSize,
                                            uint16_t packetId );

/**
 * @brief Function to validate #MQTT_Publish parameters.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] packetId Packet Id for the MQTT PUBLISH packet.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId );

/**
 * @brief Performs matching for special cases when a topic filter ends
 * with a wildcard character.
 *
 * When the topic name has been consumed but there are remaining characters to
 * to match in topic filter, this function handles the following 2 cases:
 * - When the topic filter ends with "/+" or "/#" characters, but the topic
 * name only ends with '/'.
 * - When the topic filter ends with "/#" characters, but the topic name
 * ends at the parent level.
 *
 * @note This function ASSUMES that the topic name been consumed in linear
 * matching with the topic filer, but the topic filter has remaining characters
 * to be matched.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] topicFilterLength Length of the topic filter being examined.
 * @param[in] filterIndex Index of the topic filter being examined.
 *
 * @return Returns whether the topic filter and the topic name match.
 */
static bool matchEndWildcardsSpecialCases( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           uint16_t filterIndex );

/**
 * @brief Attempt to match topic name with a topic filter starting with a wildcard.
 *
 * If the topic filter starts with a '+' (single-level) wildcard, the function
 * advances the @a pNameIndex by a level in the topic name.
 * If the topic filter starts with a '#' (multi-level) wildcard, the function
 * concludes that both the topic name and topic filter match.
 *
 * @param[in] pTopicName The topic name to match.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to match.
 * @param[in] topicFilterLength Length of the topic filter.
 * @param[in,out] pNameIndex Current index in the topic name being examined. It is
 * advanced by one level for `+` wildcards.
 * @param[in, out] pFilterIndex Current index in the topic filter being examined.
 * It is advanced to position of '/' level separator for '+' wildcard.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the
 * caller should continue parsing the topics.
 */
static bool matchWildcards( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char * pTopicFilter,
                            uint16_t topicFilterLength,
                            uint16_t * pNameIndex,
                            uint16_t * pFilterIndex,
                            bool * pMatch );

/**
 * @brief Match a topic name and topic filter allowing the use of wildcards.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of topic filter.
 *
 * @return `true` if the topic name and topic filter match; `false` otherwise.
 */
static bool matchTopicFilter( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength );

/*-----------------------------------------------------------*/

static bool matchEndWildcardsSpecialCases( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           uint16_t filterIndex )
{
    bool matchFound = false;

    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0U );

    /* Check if the topic filter has 2 remaining characters and it ends in
     * "/#". This check handles the case to match filter "sport/#" with topic
     * "sport". The reason is that the '#' wildcard represents the parent and
     * any number of child levels in the topic name.*/
    if( ( topicFilterLength >= 3U ) &&
        ( filterIndex == ( topicFilterLength - 3U ) ) &&
        ( pTopicFilter[ filterIndex + 1U ] == '/' ) &&
        ( pTopicFilter[ filterIndex + 2U ] == '#' ) )

    {
        matchFound = true;
    }

    /* Check if the next character is "#" or "+" and the topic filter ends in
     * "/#" or "/+". This check handles the cases to match:
     *
     * - Topic filter "sport/+" with topic "sport/".
     * - Topic filter "sport/#" with topic "sport/".
     */
    if( ( filterIndex == ( topicFilterLength - 2U ) ) &&
        ( pTopicFilter[ filterIndex ] == '/' ) )
    {
        /* Check that the last character is a wildcard. */
        matchFound = ( pTopicFilter[ filterIndex + 1U ] == '+' ) ||
                     ( pTopicFilter[ filterIndex + 1U ] == '#' );
    }

    return matchFound;
}

/*-----------------------------------------------------------*/

static bool matchWildcards( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char * pTopicFilter,
                            uint16_t topicFilterLength,
                            uint16_t * pNameIndex,
                            uint16_t * pFilterIndex,
                            bool * pMatch )
{
    bool shouldStopMatching = false;
    bool locationIsValidForWildcard;

    assert( pTopicName != NULL );
    assert( topicNameLength != 0U );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0U );
    assert( pNameIndex != NULL );
    assert( pFilterIndex != NULL );
    assert( pMatch != NULL );

    /* Wild card in a topic filter is only valid either at the starting position
     * or when it is preceded by a '/'.*/
    locationIsValidForWildcard = ( *pFilterIndex == 0u ) ||
                                 ( pTopicFilter[ *pFilterIndex - 1U ] == '/' );

    if( ( pTopicFilter[ *pFilterIndex ] == '+' ) && ( locationIsValidForWildcard == true ) )
    {
        bool nextLevelExistsInTopicName = false;
        bool nextLevelExistsinTopicFilter = false;

        /* Move topic name index to the end of the current level. The end of the
         * current level is identified by the last character before the next level
         * separator '/'. */
        while( *pNameIndex < topicNameLength )
        {
            /* Exit the loop if we hit the level separator. */
            if( pTopicName[ *pNameIndex ] == '/' )
            {
                nextLevelExistsInTopicName = true;
                break;
            }

            ( *pNameIndex )++;
        }

        /* Determine if the topic filter contains a child level after the current level
         * represented by the '+' wildcard. */
        if( ( *pFilterIndex < ( topicFilterLength - 1U ) ) &&
            ( pTopicFilter[ *pFilterIndex + 1U ] == '/' ) )
        {
            nextLevelExistsinTopicFilter = true;
        }

        /* If the topic name contains a child level but the topic filter ends at
         * the current level, then there does not exist a match. */
        if( ( nextLevelExistsInTopicName == true ) &&
            ( nextLevelExistsinTopicFilter == false ) )
        {
            *pMatch = false;
            shouldStopMatching = true;
        }

        /* If the topic name and topic filter have child levels, then advance the
         * filter index to the level separator in the topic filter, so that match
         * can be performed in the next level.
         * Note: The name index already points to the level separator in the topic
         * name. */
        else if( nextLevelExistsInTopicName == true )
        {
            ( *pFilterIndex )++;
        }
        else
        {
            /* If we have reached here, the the loop terminated on the
             * ( *pNameIndex < topicNameLength) condition, which means that have
             * reached past the end of the topic name, and thus, we decrement the
             * index to the last character in the topic name.*/
            ( *pNameIndex )--;
        }
    }

    /* '#' matches everything remaining in the topic name. It must be the
     * last character in a topic filter. */
    else if( ( pTopicFilter[ *pFilterIndex ] == '#' ) &&
             ( *pFilterIndex == ( topicFilterLength - 1U ) ) &&
             ( locationIsValidForWildcard == true ) )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        shouldStopMatching = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        shouldStopMatching = true;
    }

    return shouldStopMatching;
}

/*-----------------------------------------------------------*/

static bool matchTopicFilter( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength )
{
    bool matchFound = false, shouldStopMatching = false;
    uint16_t nameIndex = 0, filterIndex = 0;

    assert( pTopicName != NULL );
    assert( topicNameLength != 0 );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* If the topic name has been consumed but the topic filter has not
             * been consumed, match for special cases when the topic filter ends
             * with wildcard character. */
            if( nameIndex == ( topicNameLength - 1U ) )
            {
                matchFound = matchEndWildcardsSpecialCases( pTopicFilter,
                                                            topicFilterLength,
                                                            filterIndex );
            }
        }
        else
        {
            /* Check for matching wildcards. */
            shouldStopMatching = matchWildcards( pTopicName,
                                                 topicNameLength,
                                                 pTopicFilter,
                                                 topicFilterLength,
                                                 &nameIndex,
                                                 &filterIndex,
                                                 &matchFound );
        }

        if( ( matchFound == true ) || ( shouldStopMatching == true ) )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( matchFound == false )
    {
        /* If the end of both strings has been reached, they match. This represents the
         * case when the topic filter contains the '+' wildcard at a non-starting position.
         * For example, when matching either of "sport/+/player" OR "sport/hockey/+" topic
         * filters with "sport/hockey/player" topic name. */
        matchFound = ( nameIndex == topicNameLength ) &&
                     ( filterIndex == topicFilterLength );
    }

    return matchFound;
}

/*-----------------------------------------------------------*/

static int32_t sendMessageVector( MQTTContext_t * pContext,
                                  TransportOutVector_t * pIoVec,
                                  size_t ioVecCount )
{
    int32_t sendResult;
    uint32_t startTime;
    TransportOutVector_t * pIoVectIterator;
    size_t vectorsToBeSent = ioVecCount;
    size_t bytesToSend = 0U;
    int32_t bytesSentOrError = 0;

    assert( pContext != NULL );
    assert( pIoVec != NULL );
    assert( pContext->getTime != NULL );
    /* Send must always be defined */
    assert( pContext->transportInterface.send != NULL );

    /* Count the total number of bytes to be sent as outlined in the vector. */
    for( pIoVectIterator = pIoVec; pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ); pIoVectIterator++ )
    {
        bytesToSend += pIoVectIterator->iov_len;
    }

    /* Reset the iterator to point to the first entry in the array. */
    pIoVectIterator = pIoVec;

    /* Note the start time. */
    startTime = pContext->getTime();

    while( ( bytesSentOrError < ( int32_t ) bytesToSend ) && ( bytesSentOrError >= 0 ) )
    {
        if( pContext->transportInterface.writev != NULL )
        {
            sendResult = pContext->transportInterface.writev( pContext->transportInterface.pNetworkContext,
                                                              pIoVectIterator,
                                                              vectorsToBeSent );
        }
        else
        {
            sendResult = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                            pIoVectIterator->iov_base,
                                                            pIoVectIterator->iov_len );
        }

        if( sendResult > 0 )
        {
            /* It is a bug in the application's transport send implementation if
             * more bytes than expected are sent. */
            assert( sendResult <= ( ( int32_t ) bytesToSend - bytesSentOrError ) );

            bytesSentOrError += sendResult;

            /* Set last transmission time. */
            pContext->lastPacketTxTime = pContext->getTime();

            LogDebug( ( "sendMessageVector: Bytes Sent=%ld, Bytes Remaining=%lu",
                        ( long int ) sendResult,
                        ( unsigned long ) ( bytesToSend - ( size_t ) bytesSentOrError ) ) );
        }
        else if( sendResult < 0 )
        {
            bytesSentOrError = sendResult;
            LogError( ( "sendMessageVector: Unable to send packet: Network Error." ) );
        }
        else
        {
            /* MISRA Empty body */
        }

        /* Check for timeout. */
        if( calculateElapsedTime( pContext->getTime(), startTime ) > MQTT_SEND_TIMEOUT_MS )
        {
            LogError( ( "sendMessageVector: Unable to send packet: Timed out." ) );
            break;
        }

        /* Update the send pointer to the correct vector and offset. */
        while( ( pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ) ) &&
               ( sendResult >= ( int32_t ) pIoVectIterator->iov_len ) )
        {
            sendResult -= ( int32_t ) pIoVectIterator->iov_len;
            pIoVectIterator++;
            /* Update the number of vector which are yet to be sent. */
            vectorsToBeSent--;
        }

        /* Some of the bytes from this vector were sent as well, update the length
         * and the pointer to data in this vector. */
        if( ( sendResult > 0 ) &&
            ( pIoVectIterator <= &( pIoVec[ ioVecCount - 1U ] ) ) )
        {
            pIoVectIterator->iov_base = ( const void * ) &( ( ( const uint8_t * ) pIoVectIterator->iov_base )[ sendResult ] );
            pIoVectIterator->iov_len -= ( size_t ) sendResult;
        }
    }

    return bytesSentOrError;
}

static int32_t sendBuffer( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    int32_t sendResult;
    uint32_t startTime;
    int32_t bytesSentOrError = 0;
    const uint8_t * pIndex = pBufferToSend;

    assert( pContext != NULL );
    assert( pContext->getTime != NULL );
    assert( pContext->transportInterface.send != NULL );
    assert( pIndex != NULL );

    /* Set the timeout. */
    startTime = pContext->getTime();

    while( ( bytesSentOrError < ( int32_t ) bytesToSend ) && ( bytesSentOrError >= 0 ) )
    {
        sendResult = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                        pIndex,
                                                        bytesToSend - ( size_t ) bytesSentOrError );

        if( sendResult > 0 )
        {
            /* It is a bug in the application's transport send implementation if
             * more bytes than expected are sent. */
            assert( sendResult <= ( ( int32_t ) bytesToSend - bytesSentOrError ) );

            bytesSentOrError += sendResult;
            pIndex = &pIndex[ sendResult ];

            /* Set last transmission time. */
            pContext->lastPacketTxTime = pContext->getTime();

            LogDebug( ( "sendBuffer: Bytes Sent=%ld, Bytes Remaining=%lu",
                        ( long int ) sendResult,
                        ( unsigned long ) ( bytesToSend - ( size_t ) bytesSentOrError ) ) );
        }
        else if( sendResult < 0 )
        {
            bytesSentOrError = sendResult;
            LogError( ( "sendBuffer: Unable to send packet: Network Error." ) );
        }
        else
        {
            /* MISRA Empty body */
        }

        /* Check for timeout. */
        if( calculateElapsedTime( pContext->getTime(), startTime ) >= ( MQTT_SEND_TIMEOUT_MS ) )
        {
            LogError( ( "sendBuffer: Unable to send packet: Timed out." ) );
            break;
        }
    }

    return bytesSentOrError;
}

/*-----------------------------------------------------------*/

static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}

/*-----------------------------------------------------------*/

static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType )
{
    MQTTPubAckType_t ackType = MQTTPuback;

    switch( packetType )
    {
        case MQTT_PACKET_TYPE_PUBACK:
            ackType = MQTTPuback;
            break;

        case MQTT_PACKET_TYPE_PUBREC:
            ackType = MQTTPubrec;
            break;

        case MQTT_PACKET_TYPE_PUBREL:
            ackType = MQTTPubrel;
            break;

        case MQTT_PACKET_TYPE_PUBCOMP:
        default:

            /* This function is only called after checking the type is one of
             * the above four values, so packet type must be PUBCOMP here. */
            assert( packetType == MQTT_PACKET_TYPE_PUBCOMP );
            ackType = MQTTPubcomp;
            break;
    }

    return ackType;
}

/*-----------------------------------------------------------*/

static int32_t recvExact( const MQTTContext_t * pContext,
                          size_t bytesToRecv )
{
    uint8_t * pIndex = NULL;
    size_t bytesRemaining = bytesToRecv;
    int32_t totalBytesRecvd = 0, bytesRecvd;
    uint32_t lastDataRecvTimeMs = 0U, timeSinceLastRecvMs = 0U;
    TransportRecv_t recvFunc = NULL;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    bool receiveError = false;

    assert( pContext != NULL );
    assert( bytesToRecv <= pContext->networkBuffer.size );
    assert( pContext->getTime != NULL );
    assert( pContext->transportInterface.recv != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );

    pIndex = pContext->networkBuffer.pBuffer;
    recvFunc = pContext->transportInterface.recv;
    getTimeStampMs = pContext->getTime;

    /* Part of the MQTT packet has been read before calling this function. */
    lastDataRecvTimeMs = getTimeStampMs();

    while( ( bytesRemaining > 0U ) && ( receiveError == false ) )
    {
        bytesRecvd = recvFunc( pContext->transportInterface.pNetworkContext,
                               pIndex,
                               bytesRemaining );

        if( bytesRecvd < 0 )
        {
            LogError( ( "Network error while receiving packet: ReturnCode=%ld.",
                        ( long int ) bytesRecvd ) );
            totalBytesRecvd = bytesRecvd;
            receiveError = true;
        }
        else if( bytesRecvd > 0 )
        {
            /* Reset the starting time as we have received some data from the network. */
            lastDataRecvTimeMs = getTimeStampMs();

            /* It is a bug in the application's transport receive implementation
             * if more bytes than expected are received. To avoid a possible
             * overflow in converting bytesRemaining from unsigned to signed,
             * this assert must exist after the check for bytesRecvd being
             * negative. */
            assert( ( size_t ) bytesRecvd <= bytesRemaining );

            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += ( int32_t ) bytesRecvd;
            /* Increment the index. */
            pIndex = &pIndex[ bytesRecvd ];
            LogDebug( ( "BytesReceived=%ld, BytesRemaining=%lu, TotalBytesReceived=%ld.",
                        ( long int ) bytesRecvd,
                        ( unsigned long ) bytesRemaining,
                        ( long int ) totalBytesRecvd ) );
        }
        else
        {
            /* No bytes were read from the network. */
            timeSinceLastRecvMs = calculateElapsedTime( getTimeStampMs(), lastDataRecvTimeMs );

            /* Check for timeout if we have been waiting to receive any byte on the network. */
            if( timeSinceLastRecvMs >= MQTT_RECV_POLLING_TIMEOUT_MS )
            {
                LogError( ( "Unable to receive packet: Timed out in transport recv." ) );
                receiveError = true;
            }
        }
    }

    return totalBytesRecvd;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t discardPacket( const MQTTContext_t * pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTRecvFailed;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;
    uint32_t totalBytesReceived = 0U;
    uint32_t entryTimeMs = 0U;
    uint32_t elapsedTimeMs = 0U;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = NULL;
    bool receiveError = false;

    assert( pContext != NULL );
    assert( pContext->getTime != NULL );

    bytesToReceive = pContext->networkBuffer.size;
    getTimeStampMs = pContext->getTime;

    entryTimeMs = getTimeStampMs();

    while( ( totalBytesReceived < remainingLength ) && ( receiveError == false ) )
    {
        if( ( remainingLength - totalBytesReceived ) < bytesToReceive )
        {
            bytesToReceive = remainingLength - totalBytesReceived;
        }

        bytesReceived = recvExact( pContext, bytesToReceive );

        if( bytesReceived != ( int32_t ) bytesToReceive )
        {
            LogError( ( "Receive error while discarding packet."
                        "ReceivedBytes=%ld, ExpectedBytes=%lu.",
                        ( long int ) bytesReceived,
                        ( unsigned long ) bytesToReceive ) );
            receiveError = true;
        }
        else
        {
            totalBytesReceived += ( uint32_t ) bytesReceived;

            elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

            /* Check for timeout. */
            if( elapsedTimeMs >= timeoutMs )
            {
                LogError( ( "Time expired while discarding packet." ) );
                receiveError = true;
            }
        }
    }

    if( totalBytesReceived == remainingLength )
    {
        LogError( ( "Dumped packet. DumpedBytes=%lu.",
                    ( unsigned long ) totalBytesReceived ) );
        /* Packet dumped, so no data is available. */
        status = MQTTNoDataAvailable;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t discardStoredPacket( MQTTContext_t * pContext,
                                         const MQTTPacketInfo_t * pPacketInfo )
{
    MQTTStatus_t status = MQTTRecvFailed;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;
    uint32_t totalBytesReceived = 0U;
    bool receiveError = false;
    size_t mqttPacketSize = 0;
    size_t remainingLength;

    assert( pContext != NULL );
    assert( pPacketInfo != NULL );

    mqttPacketSize = pPacketInfo->remainingLength + pPacketInfo->headerLength;

    /* Assert that the packet being discarded is bigger than the
     * receive buffer. */
    assert( mqttPacketSize > pContext->networkBuffer.size );

    /* Discard these many bytes at a time. */
    bytesToReceive = pContext->networkBuffer.size;

    /* Number of bytes depicted by 'index' have already been received. */
    remainingLength = mqttPacketSize - pContext->index;

    while( ( totalBytesReceived < remainingLength ) && ( receiveError == false ) )
    {
        if( ( remainingLength - totalBytesReceived ) < bytesToReceive )
        {
            bytesToReceive = remainingLength - totalBytesReceived;
        }

        bytesReceived = recvExact( pContext, bytesToReceive );

        if( bytesReceived != ( int32_t ) bytesToReceive )
        {
            LogError( ( "Receive error while discarding packet."
                        "ReceivedBytes=%ld, ExpectedBytes=%lu.",
                        ( long int ) bytesReceived,
                        ( unsigned long ) bytesToReceive ) );
            receiveError = true;
        }
        else
        {
            totalBytesReceived += ( uint32_t ) bytesReceived;
        }
    }

    if( totalBytesReceived == remainingLength )
    {
        LogError( ( "Dumped packet. DumpedBytes=%lu.",
                    ( unsigned long ) totalBytesReceived ) );
        /* Packet dumped, so no data is available. */
        status = MQTTNoDataAvailable;
    }

    /* Clear the buffer */
    ( void ) memset( pContext->networkBuffer.pBuffer,
                     0,
                     pContext->networkBuffer.size );

    /* Reset the index. */
    pContext->index = 0;

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receivePacket( const MQTTContext_t * pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;

    assert( pContext != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );

    if( incomingPacket.remainingLength > pContext->networkBuffer.size )
    {
        LogError( ( "Incoming packet will be dumped: "
                    "Packet length exceeds network buffer size."
                    "PacketSize=%lu, NetworkBufferSize=%lu.",
                    ( unsigned long ) incomingPacket.remainingLength,
                    ( unsigned long ) pContext->networkBuffer.size ) );
        status = discardPacket( pContext,
                                incomingPacket.remainingLength,
                                remainingTimeMs );
    }
    else
    {
        bytesToReceive = incomingPacket.remainingLength;
        bytesReceived = recvExact( pContext, bytesToReceive );

        if( bytesReceived == ( int32_t ) bytesToReceive )
        {
            /* Receive successful, bytesReceived == bytesToReceive. */
            LogDebug( ( "Packet received. ReceivedBytes=%ld.",
                        ( long int ) bytesReceived ) );
        }
        else
        {
            LogError( ( "Packet reception failed. ReceivedBytes=%ld, "
                        "ExpectedBytes=%lu.",
                        ( long int ) bytesReceived,
                        ( unsigned long ) bytesToReceive ) );
            status = MQTTRecvFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static uint8_t getAckTypeToSend( MQTTPublishState_t state )
{
    uint8_t packetTypeByte = 0U;

    switch( state )
    {
        case MQTTPubAckSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBACK;
            break;

        case MQTTPubRecSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREC;
            break;

        case MQTTPubRelSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBREL;
            break;

        case MQTTPubCompSend:
            packetTypeByte = MQTT_PACKET_TYPE_PUBCOMP;
            break;

        case MQTTPubAckPending:
        case MQTTPubCompPending:
        case MQTTPubRecPending:
        case MQTTPubRelPending:
        case MQTTPublishDone:
        case MQTTPublishSend:
        case MQTTStateNull:
        default:
            /* Take no action for states that do not require sending an ack. */
            break;
    }

    return packetTypeByte;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishAcks( MQTTContext_t * pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    int32_t sendResult = 0;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;
    MQTTFixedBuffer_t localBuffer;
    uint8_t pubAckPacket[ MQTT_PUBLISH_ACK_PACKET_SIZE ];

    localBuffer.pBuffer = pubAckPacket;
    localBuffer.size = MQTT_PUBLISH_ACK_PACKET_SIZE;

    assert( pContext != NULL );

    packetTypeByte = getAckTypeToSend( publishState );

    if( packetTypeByte != 0U )
    {
        packetType = getAckFromPacketType( packetTypeByte );

        status = MQTT_SerializeAck( &localBuffer,
                                    packetTypeByte,
                                    packetId );

        if( status == MQTTSuccess )
        {
            MQTT_PRE_SEND_HOOK( pContext );

            /* Here, we are not using the vector approach for efficiency. There is just one buffer
             * to be sent which can be achieved with a normal send call. */
            sendResult = sendBuffer( pContext,
                                     localBuffer.pBuffer,
                                     MQTT_PUBLISH_ACK_PACKET_SIZE );

            MQTT_POST_SEND_HOOK( pContext );
        }

        if( sendResult == ( int32_t ) MQTT_PUBLISH_ACK_PACKET_SIZE )
        {
            pContext->controlPacketSent = true;

            MQTT_PRE_STATE_UPDATE_HOOK( pContext );

            status = MQTT_UpdateStateAck( pContext,
                                          packetId,
                                          packetType,
                                          MQTT_SEND,
                                          &newState );

            MQTT_POST_STATE_UPDATE_HOOK( pContext );

            if( status != MQTTSuccess )
            {
                LogError( ( "Failed to update state of publish %hu.",
                            ( unsigned short ) packetId ) );
            }
        }
        else
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, SentBytes=%ld, "
                        "PacketSize=%lu.",
                        ( unsigned int ) packetTypeByte, ( long int ) sendResult,
                        MQTT_PUBLISH_ACK_PACKET_SIZE ) );
            status = MQTTSendFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleKeepAlive( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t now = 0U;
    uint32_t packetTxTimeoutMs = 0U;
    uint32_t lastPacketTxTime = 0U;

    assert( pContext != NULL );
    assert( pContext->getTime != NULL );

    now = pContext->getTime();

    packetTxTimeoutMs = 1000U * ( uint32_t ) pContext->keepAliveIntervalSec;

    if( PACKET_TX_TIMEOUT_MS < packetTxTimeoutMs )
    {
        packetTxTimeoutMs = PACKET_TX_TIMEOUT_MS;
    }

    /* If keep alive interval is 0, it is disabled. */
    if( pContext->waitingForPingResp == true )
    {
        /* Has time expired? */
        if( calculateElapsedTime( now, pContext->pingReqSendTimeMs ) >
            MQTT_PINGRESP_TIMEOUT_MS )
        {
            status = MQTTKeepAliveTimeout;
        }
    }
    else
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );
        lastPacketTxTime = pContext->lastPacketTxTime;
        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( ( packetTxTimeoutMs != 0U ) && ( calculateElapsedTime( now, lastPacketTxTime ) >= packetTxTimeoutMs ) )
        {
            status = MQTT_Ping( pContext );
        }
        else
        {
            const uint32_t timeElapsed = calculateElapsedTime( now, pContext->lastPacketRxTime );

            if( ( timeElapsed != 0U ) && ( timeElapsed >= PACKET_RX_TIMEOUT_MS ) )
            {
                status = MQTT_Ping( pContext );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingPublish( MQTTContext_t * pContext,
                                           MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier = 0U;
    MQTTPublishInfo_t publishInfo;
    MQTTDeserializedInfo_t deserializedInfo;
    bool duplicatePublish = false;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    status = MQTT_DeserializePublish( pIncomingPacket, &packetIdentifier, &publishInfo );
    LogInfo( ( "De-serialized incoming PUBLISH packet: DeserializerResult=%s.",
               MQTT_Status_strerror( status ) ) );

    if( ( status == MQTTSuccess ) &&
        ( pContext->incomingPublishRecords == NULL ) &&
        ( publishInfo.qos > MQTTQoS0 ) )
    {
        LogError( ( "Incoming publish has QoS > MQTTQoS0 but incoming "
                    "publish records have not been initialized. Dropping the "
                    "incoming publish. Please call MQTT_InitStatefulQoS to enable "
                    "use of QoS1 and QoS2 publishes." ) );
        status = MQTTRecvFailed;
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        status = MQTT_UpdateStatePublish( pContext,
                                          packetIdentifier,
                                          MQTT_RECEIVE,
                                          publishInfo.qos,
                                          &publishRecordState );

        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }

        /* Different cases in which an incoming publish with duplicate flag is
         * handled are as listed below.
         * 1. No collision - This is the first instance of the incoming publish
         *    packet received or an earlier received packet state is lost. This
         *    will be handled as a new incoming publish for both QoS1 and QoS2
         *    publishes.
         * 2. Collision - The incoming packet was received before and a state
         *    record is present in the state engine. For QoS1 and QoS2 publishes
         *    this case can happen at 2 different cases and handling is
         *    different.
         *    a. QoS1 - If a PUBACK is not successfully sent for the incoming
         *       publish due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by processing the incoming
         *       publish as a new publish ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application.
         *    b. QoS2 - If a PUBREC is not successfully sent for the incoming
         *       publish or the PUBREC sent is not successfully received by the
         *       broker due to a connection issue, it can result in broker
         *       sending out a duplicate publish with dup flag set, when a
         *       session is reestablished. It can result in a collision in
         *       state engine. This will be handled by ignoring the
         *       #MQTTStateCollision status from the state engine. The publish
         *       data is not passed to the application. */
        else if( status == MQTTStateCollision )
        {
            status = MQTTSuccess;
            duplicatePublish = true;

            /* Calculate the state for the ack packet that needs to be sent out
             * for the duplicate incoming publish. */
            publishRecordState = MQTT_CalculateStatePublish( MQTT_RECEIVE,
                                                             publishInfo.qos );

            LogDebug( ( "Incoming publish packet with packet id %hu already exists.",
                        ( unsigned short ) packetIdentifier ) );

            if( publishInfo.dup == false )
            {
                LogError( ( "DUP flag is 0 for duplicate packet (MQTT-3.3.1.-1)." ) );
            }
        }
        else
        {
            LogError( ( "Error in updating publish state for incoming publish with packet id %hu."
                        " Error is %s",
                        ( unsigned short ) packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Set fields of deserialized struct. */
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.pPublishInfo = &publishInfo;
        deserializedInfo.deserializationResult = status;

        /* Invoke application callback to hand the buffer over to application
         * before sending acks.
         * Application callback will be invoked for all publishes, except for
         * duplicate incoming publishes. */
        if( duplicatePublish == false )
        {
            pContext->appCallback( pContext,
                                   pIncomingPacket,
                                   &deserializedInfo );
        }

        /* Send PUBACK or PUBREC if necessary. */
        status = sendPublishAcks( pContext,
                                  packetIdentifier,
                                  publishRecordState );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handlePublishAcks( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadResponse;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier;
    MQTTPubAckType_t ackType;
    MQTTEventCallback_t appCallback;
    MQTTDeserializedInfo_t deserializedInfo;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    appCallback = pContext->appCallback;

    ackType = getAckFromPacketType( pIncomingPacket->type );
    status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
    LogInfo( ( "Ack packet deserialized with result: %s.",
               MQTT_Status_strerror( status ) ) );

    if( status == MQTTSuccess )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        status = MQTT_UpdateStateAck( pContext,
                                      packetIdentifier,
                                      ackType,
                                      MQTT_RECEIVE,
                                      &publishRecordState );

        MQTT_POST_STATE_UPDATE_HOOK( pContext );

        if( status == MQTTSuccess )
        {
            LogInfo( ( "State record updated. New state=%s.",
                       MQTT_State_strerror( publishRecordState ) ) );
        }
        else
        {
            LogError( ( "Updating the state engine for packet id %hu"
                        " failed with error %s.",
                        ( unsigned short ) packetIdentifier,
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Set fields of deserialized struct. */
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.deserializationResult = status;
        deserializedInfo.pPublishInfo = NULL;

        /* Invoke application callback to hand the buffer over to application
         * before sending acks. */
        appCallback( pContext, pIncomingPacket, &deserializedInfo );

        /* Send PUBREL or PUBCOMP if necessary. */
        status = sendPublishAcks( pContext,
                                  packetIdentifier,
                                  publishRecordState );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleIncomingAck( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pIncomingPacket,
                                       bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTBadResponse;
    uint16_t packetIdentifier = MQTT_PACKET_ID_INVALID;
    MQTTDeserializedInfo_t deserializedInfo;

    /* We should always invoke the app callback unless we receive a PINGRESP
     * and are managing keep alive, or if we receive an unknown packet. We
     * initialize this to false since the callback must be invoked before
     * sending any PUBREL or PUBCOMP. However, for other cases, we invoke it
     * at the end to reduce the complexity of this function. */
    bool invokeAppCallback = false;
    MQTTEventCallback_t appCallback = NULL;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->appCallback != NULL );

    appCallback = pContext->appCallback;

    LogDebug( ( "Received packet of type %02x.",
                ( unsigned int ) pIncomingPacket->type ) );

    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBREL:
        case MQTT_PACKET_TYPE_PUBCOMP:

            /* Handle all the publish acks. The app callback is invoked here. */
            status = handlePublishAcks( pContext, pIncomingPacket );

            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
            invokeAppCallback = ( status == MQTTSuccess ) && !manageKeepAlive;

            if( ( status == MQTTSuccess ) && ( manageKeepAlive == true ) )
            {
                pContext->waitingForPingResp = false;
            }

            break;

        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
            /* Deserialize and give these to the app provided callback. */
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, NULL );
            invokeAppCallback = ( status == MQTTSuccess ) || ( status == MQTTServerRefused );
            break;

        default:
            /* Bad response from the server. */
            LogError( ( "Unexpected packet type from server: PacketType=%02x.",
                        ( unsigned int ) pIncomingPacket->type ) );
            status = MQTTBadResponse;
            break;
    }

    if( invokeAppCallback == true )
    {
        /* Set fields of deserialized struct. */
        deserializedInfo.packetIdentifier = packetIdentifier;
        deserializedInfo.deserializationResult = status;
        deserializedInfo.pPublishInfo = NULL;
        appCallback( pContext, pIncomingPacket, &deserializedInfo );
        /* In case a SUBACK indicated refusal, reset the status to continue the loop. */
        status = MQTTSuccess;
    }

    return status;
}
/*-----------------------------------------------------------*/

static MQTTStatus_t receiveSingleIteration( MQTTContext_t * pContext,
                                            bool manageKeepAlive )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    int32_t recvBytes;
    size_t totalMQTTPacketLength = 0;

    assert( pContext != NULL );
    assert( pContext->networkBuffer.pBuffer != NULL );

    /* Read as many bytes as possible into the network buffer. */
    recvBytes = pContext->transportInterface.recv( pContext->transportInterface.pNetworkContext,
                                                   &( pContext->networkBuffer.pBuffer[ pContext->index ] ),
                                                   pContext->networkBuffer.size - pContext->index );

    if( recvBytes < 0 )
    {
        /* The receive function has failed. Bubble up the error up to the user. */
        status = MQTTRecvFailed;
    }
    else if( ( recvBytes == 0 ) && ( pContext->index == 0U ) )
    {
        /* No more bytes available since the last read and neither is anything in
         * the buffer. */
        status = MQTTNoDataAvailable;
    }

    /* Either something was received, or there is still data to be processed in the
     * buffer, or both. */
    else
    {
        /* Update the number of bytes in the MQTT fixed buffer. */
        pContext->index += ( size_t ) recvBytes;

        status = MQTT_ProcessIncomingPacketTypeAndLength( pContext->networkBuffer.pBuffer,
                                                          &( pContext->index ),
                                                          &incomingPacket );

        totalMQTTPacketLength = incomingPacket.remainingLength + incomingPacket.headerLength;
    }

    /* No data was received, check for keep alive timeout. */
    if( recvBytes == 0 )
    {
        if( manageKeepAlive == true )
        {
            /* Keep the copy of the status to be reset later. */
            MQTTStatus_t statusCopy = status;

            /* Assign status so an error can be bubbled up to application,
             * but reset it on success. */
            status = handleKeepAlive( pContext );

            if( status == MQTTSuccess )
            {
                /* Reset the status. */
                status = statusCopy;
            }
            else
            {
                LogError( ( "Handling of keep alive failed. Status=%s",
                            MQTT_Status_strerror( status ) ) );
            }
        }
    }

    /* Check whether there is data available before processing the packet further. */
    if( ( status == MQTTNeedMoreBytes ) || ( status == MQTTNoDataAvailable ) )
    {
        /* Do nothing as there is nothing to be processed right now. The proper
         * error code will be bubbled up to the user. */
    }
    /* Any other error code. */
    else if( status != MQTTSuccess )
    {
        LogError( ( "Call to receiveSingleIteration failed. Status=%s",
                    MQTT_Status_strerror( status ) ) );
    }
    /* If the MQTT Packet size is bigger than the buffer itself. */
    else if( totalMQTTPacketLength > pContext->networkBuffer.size )
    {
        /* Discard the packet from the receive buffer and drain the pending
         * data from the socket buffer. */
        status = discardStoredPacket( pContext,
                                      &incomingPacket );
    }
    /* If the total packet is of more length than the bytes we have available. */
    else if( totalMQTTPacketLength > pContext->index )
    {
        status = MQTTNeedMoreBytes;
    }
    else
    {
        /* MISRA else. */
    }

    /* Handle received packet. If incomplete data was read then this will not execute. */
    if( status == MQTTSuccess )
    {
        incomingPacket.pRemainingData = &pContext->networkBuffer.pBuffer[ incomingPacket.headerLength ];

        /* PUBLISH packets allow flags in the lower four bits. For other
         * packet types, they are reserved. */
        if( ( incomingPacket.type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
        {
            status = handleIncomingPublish( pContext, &incomingPacket );
        }
        else
        {
            status = handleIncomingAck( pContext, &incomingPacket, manageKeepAlive );
        }

        /* Update the index to reflect the remaining bytes in the buffer.  */
        pContext->index -= totalMQTTPacketLength;

        /* Move the remaining bytes to the front of the buffer. */
        ( void ) memmove( pContext->networkBuffer.pBuffer,
                          &( pContext->networkBuffer.pBuffer[ totalMQTTPacketLength ] ),
                          pContext->index );

        if( status == MQTTSuccess )
        {
            pContext->lastPacketRxTime = pContext->getTime();
        }
    }

    if( status == MQTTNoDataAvailable )
    {
        /* No data available is not an error. Reset to MQTTSuccess so the
         * return code will indicate success. */
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * pContext,
                                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t iterator;

    /* Validate all the parameters. */
    if( ( pContext == NULL ) || ( pSubscriptionList == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pSubscriptionList=%p.",
                    ( void * ) pContext,
                    ( void * ) pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0UL )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {
        if( pContext->incomingPublishRecords == NULL )
        {
            for( iterator = 0; iterator < subscriptionCount; iterator++ )
            {
                if( pSubscriptionList->qos > MQTTQoS0 )
                {
                    LogError( ( "The incoming publish record list is not "
                                "initialised for QoS1/QoS2 records. Please call "
                                " MQTT_InitStatefulQoS to enable use of QoS1 and "
                                " QoS2 packets." ) );
                    status = MQTTBadParameter;
                    break;
                }
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static size_t addEncodedStringToVector( uint8_t serializedLength[ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ],
                                        const char * const string,
                                        uint16_t length,
                                        TransportOutVector_t * iterator,
                                        size_t * updatedLength )
{
    size_t packetLength = 0U;
    TransportOutVector_t * pLocalIterator = iterator;
    size_t vectorsAdded = 0U;

    /* When length is non-zero, the string must be non-NULL. */
    assert( ( length != 0U ) ? ( string != NULL ) : true );

    serializedLength[ 0 ] = ( ( uint8_t ) ( ( length ) >> 8 ) );
    serializedLength[ 1 ] = ( ( uint8_t ) ( ( length ) & 0x00ffU ) );

    /* Add the serialized length of the string first. */
    pLocalIterator[ 0 ].iov_base = serializedLength;
    pLocalIterator[ 0 ].iov_len = CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES;
    vectorsAdded++;
    packetLength = CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES;

    /* Sometimes the string can be NULL that is, of 0 length. In that case,
     * only the length field should be encoded in the vector. */
    if( ( string != NULL ) && ( length != 0U ) )
    {
        /* Then add the pointer to the string itself. */
        pLocalIterator[ 1 ].iov_base = string;
        pLocalIterator[ 1 ].iov_len = length;
        vectorsAdded++;
        packetLength += length;
    }

    ( *updatedLength ) = ( *updatedLength ) + packetLength;

    return vectorsAdded;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendSubscribeWithoutCopy( MQTTContext_t * pContext,
                                              const MQTTSubscribeInfo_t * pSubscriptionList,
                                              size_t subscriptionCount,
                                              uint16_t packetId,
                                              size_t remainingLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex;
    TransportOutVector_t pIoVector[ MQTT_SUB_UNSUB_MAX_VECTORS ];
    TransportOutVector_t * pIterator;
    uint8_t serializedTopicFieldLength[ MQTT_SUB_UNSUB_MAX_VECTORS ][ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ];
    size_t totalPacketLength = 0U;
    size_t ioVectorLength = 0U;
    size_t subscriptionsSent = 0U;
    size_t vectorsAdded;
    size_t topicFieldLengthIndex;

    /* Maximum number of bytes required by the 'fixed' part of the SUBSCRIBE
     * packet header according to the MQTT specification.
     * MQTT Control Byte      0 + 1 = 1
     * Remaining length (max)   + 4 = 5
     * Packet ID                + 2 = 7 */
    uint8_t subscribeheader[ 7U ];

    /* The vector array should be at least three element long as the topic
     * string needs these many vector elements to be stored. */
    assert( MQTT_SUB_UNSUB_MAX_VECTORS >= CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH );

    pIndex = subscribeheader;
    pIterator = pIoVector;

    pIndex = MQTT_SerializeSubscribeHeader( remainingLength,
                                            pIndex,
                                            packetId );

    /* The header is to be sent first. */
    pIterator->iov_base = subscribeheader;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - subscribeheader );
    totalPacketLength += pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    while( ( status == MQTTSuccess ) && ( subscriptionsSent < subscriptionCount ) )
    {
        /* Reset the index for next iteration. */
        topicFieldLengthIndex = 0;

        /* Check whether the subscription topic (with QoS) will fit in the
         * given vector. */
        while( ( ioVectorLength <= ( MQTT_SUB_UNSUB_MAX_VECTORS - CORE_MQTT_SUBSCRIBE_PER_TOPIC_VECTOR_LENGTH ) ) &&
               ( subscriptionsSent < subscriptionCount ) )
        {
            /* The topic filter and the filter length gets sent next. */
            vectorsAdded = addEncodedStringToVector( serializedTopicFieldLength[ topicFieldLengthIndex ],
                                                     pSubscriptionList[ subscriptionsSent ].pTopicFilter,
                                                     pSubscriptionList[ subscriptionsSent ].topicFilterLength,
                                                     pIterator,
                                                     &totalPacketLength );

            /* Update the pointer after the above operation. */
            pIterator = &pIterator[ vectorsAdded ];

            /* Lastly, the QoS gets sent. */
            pIterator->iov_base = &( pSubscriptionList[ subscriptionsSent ].qos );
            pIterator->iov_len = 1U;
            totalPacketLength += pIterator->iov_len;

            /* Increment the pointer. */
            pIterator++;

            /* Two slots get used by the topic string length and topic string.
             * One slot gets used by the quality of service. */
            ioVectorLength += vectorsAdded + 1U;

            subscriptionsSent++;

            /* The index needs to be updated for next iteration. */
            topicFieldLengthIndex++;
        }

        if( sendMessageVector( pContext,
                               pIoVector,
                               ioVectorLength ) != ( int32_t ) totalPacketLength )
        {
            status = MQTTSendFailed;
        }

        /* Update the iterator for the next potential loop iteration. */
        pIterator = pIoVector;
        /* Reset the vector length for the next potential loop iteration. */
        ioVectorLength = 0U;
        /* Reset the packet length for the next potential loop iteration. */
        totalPacketLength = 0U;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendUnsubscribeWithoutCopy( MQTTContext_t * pContext,
                                                const MQTTSubscribeInfo_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint16_t packetId,
                                                size_t remainingLength )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t * pIndex;
    TransportOutVector_t pIoVector[ MQTT_SUB_UNSUB_MAX_VECTORS ];
    TransportOutVector_t * pIterator;
    uint8_t serializedTopicFieldLength[ MQTT_SUB_UNSUB_MAX_VECTORS ][ CORE_MQTT_SERIALIZED_LENGTH_FIELD_BYTES ];
    size_t totalPacketLength = 0U;
    size_t unsubscriptionsSent = 0U;
    size_t ioVectorLength = 0U;
    size_t vectorsAdded;
    size_t topicFieldLengthIndex;

    /* Maximum number of bytes required by the 'fixed' part of the UNSUBSCRIBE
     * packet header according to the MQTT specification.
     * MQTT Control Byte      0 + 1 = 1
     * Remaining length (max)   + 4 = 5
     * Packet ID                + 2 = 7  */
    uint8_t unsubscribeheader[ 7U ];

    /* The vector array should be at least three element long as the topic
     * string needs these many vector elements to be stored. */
    assert( MQTT_SUB_UNSUB_MAX_VECTORS >= CORE_MQTT_UNSUBSCRIBE_PER_TOPIC_VECTOR_LENGTH );

    pIndex = unsubscribeheader;
    pIterator = pIoVector;

    pIndex = MQTT_SerializeUnsubscribeHeader( remainingLength,
                                              pIndex,
                                              packetId );

    /* The header is to be sent first. */
    pIterator->iov_base = unsubscribeheader;
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
    /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
    /* coverity[misra_c_2012_rule_18_2_violation] */
    /* coverity[misra_c_2012_rule_10_8_violation] */
    pIterator->iov_len = ( size_t ) ( pIndex - unsubscribeheader );
    totalPacketLength += pIterator->iov_len;
    pIterator++;
    ioVectorLength++;

    while( ( status == MQTTSuccess ) && ( unsubscriptionsSent < subscriptionCount ) )
    {
        /* Reset the index for next iteration. */
        topicFieldLengthIndex = 0;

        /* Check whether the subscription topic will fit in the given vector. */
        while( ( ioVectorLength <= ( MQTT_SUB_UNSUB_MAX_VECTORS - CORE_MQTT_UNSUBSCRIBE_PER_TOPIC_VECTOR_LENGTH ) ) &&
               ( unsubscriptionsSent < subscriptionCount ) )
        {
            /* The topic filter gets sent next. */
            vectorsAdded = addEncodedStringToVector( serializedTopicFieldLength[ topicFieldLengthIndex ],
                                                     pSubscriptionList[ unsubscriptionsSent ].pTopicFilter,
                                                     pSubscriptionList[ unsubscriptionsSent ].topicFilterLength,
                                                     pIterator,
                                                     &totalPacketLength );

            /* Update the iterator to point to the next empty location. */
            pIterator = &pIterator[ vectorsAdded ];
            /* Update the total count based on how many vectors were added. */
            ioVectorLength += vectorsAdded;

            unsubscriptionsSent++;

            /* Update the index for next iteration. */
            topicFieldLengthIndex++;
        }

        if( sendMessageVector( pContext, pIoVector, ioVectorLength ) != ( int32_t ) totalPacketLength )
        {
            status = MQTTSendFailed;
        }

        /* Update the iterator for the next potential loop iteration. */
        pIterator = pIoVector;
        /* Reset the vector length for the next potential loop iteration. */
        ioVectorLength = 0U;
        /* Reset the packet length for the next potential loop iteration. */
        totalPacketLength = 0U;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublishWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTPublishInfo_t * pPublishInfo,
                                            const uint8_t * pMqttHeader,
                                            size_t headerSize,
                                            uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t ioVectorLength;
    size_t totalMessageLength;

    /* Bytes required to encode the packet ID in an MQTT header according to
     * the MQTT specification. */
    uint8_t serializedPacketID[ 2U ];

    /* Maximum number of vectors required to encode and send a publish
     * packet. The breakdown is shown below.
     * Fixed header (including topic string length)      0 + 1 = 1
     * Topic string                                        + 1 = 2
     * Packet ID (only when QoS > QoS0)                    + 1 = 3
     * Payload                                             + 1 = 4  */
    TransportOutVector_t pIoVector[ 4U ];

    /* The header is sent first. */
    pIoVector[ 0U ].iov_base = pMqttHeader;
    pIoVector[ 0U ].iov_len = headerSize;
    totalMessageLength = headerSize;

    /* Then the topic name has to be sent. */
    pIoVector[ 1U ].iov_base = pPublishInfo->pTopicName;
    pIoVector[ 1U ].iov_len = pPublishInfo->topicNameLength;
    totalMessageLength += pPublishInfo->topicNameLength;

    /* The next field's index should be 2 as the first two fields
     * have been filled in. */
    ioVectorLength = 2U;

    if( pPublishInfo->qos > MQTTQoS0 )
    {
        /* Encode the packet ID. */
        serializedPacketID[ 0 ] = ( ( uint8_t ) ( ( packetId ) >> 8 ) );
        serializedPacketID[ 1 ] = ( ( uint8_t ) ( ( packetId ) & 0x00ffU ) );

        pIoVector[ ioVectorLength ].iov_base = serializedPacketID;
        pIoVector[ ioVectorLength ].iov_len = sizeof( serializedPacketID );

        ioVectorLength++;
        totalMessageLength += sizeof( serializedPacketID );
    }

    /* Publish packets are allowed to contain no payload. */
    if( pPublishInfo->payloadLength > 0U )
    {
        pIoVector[ ioVectorLength ].iov_base = pPublishInfo->pPayload;
        pIoVector[ ioVectorLength ].iov_len = pPublishInfo->payloadLength;

        ioVectorLength++;
        totalMessageLength += pPublishInfo->payloadLength;
    }

    if( sendMessageVector( pContext, pIoVector, ioVectorLength ) != ( int32_t ) totalMessageLength )
    {
        status = MQTTSendFailed;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendConnectWithoutCopy( MQTTContext_t * pContext,
                                            const MQTTConnectInfo_t * pConnectInfo,
                                            const MQTTPublishInfo_t * pWillInfo,
                                            size_t remainingLength )
{
    MQTTStatus_t status = MQTTSuccess;
    TransportOutVector_t * iterator;
    size_t ioVectorLength = 0U;
    size_t totalMessageLength = 0U;
    int32_t bytesSentOrError;
    uint8_t * pIndex;
    uint8_t serializedClientIDLength[ 2 ];
    uint8_t serializedTopicLength[ 2 ];
    uint8_t serializedPayloadLength[ 2 ];
    uint8_t serializedUsernameLength[ 2 ];
    uint8_t serializedPasswordLength[ 2 ];
    size_t vectorsAdded;

    /* Maximum number of bytes required by the 'fixed' part of the CONNECT
     * packet header according to the MQTT specification.
     * MQTT Control Byte      0 + 1 = 1
     * Remaining length (max)   + 4 = 5
     * Protocol Name Length     + 2 = 7
     * Protocol Name (MQTT)     + 4 = 11
     * Protocol level           + 1 = 12
     * Connect flags            + 1 = 13
     * Keep alive               + 2 = 15 */
    uint8_t connectPacketHeader[ 15U ];

    /* The maximum vectors required to encode and send a connect packet. The
     * breakdown is shown below.
     * Fixed header      0 + 1 = 1
     * Client ID           + 2 = 3
     * Will topic          + 2 = 5
     * Will payload        + 2 = 7
     * Username            + 2 = 9
     * Password            + 2 = 11 */
    TransportOutVector_t pIoVector[ 11U ];

    iterator = pIoVector;
    pIndex = connectPacketHeader;

    /* Validate arguments. */
    if( ( pWillInfo != NULL ) && ( pWillInfo->pTopicName == NULL ) )
    {
        LogError( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
        status = MQTTBadParameter;
    }
    else
    {
        pIndex = MQTT_SerializeConnectFixedHeader( pIndex,
                                                   pConnectInfo,
                                                   pWillInfo,
                                                   remainingLength );

        assert( ( ( size_t ) ( pIndex - connectPacketHeader ) ) <= sizeof( connectPacketHeader ) );

        /* The header gets sent first. */
        iterator->iov_base = connectPacketHeader;
        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-182 */
        /* More details at: https://github.com/FreeRTOS/coreMQTT/blob/main/MISRA.md#rule-108 */
        /* coverity[misra_c_2012_rule_18_2_violation] */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        iterator->iov_len = ( size_t ) ( pIndex - connectPacketHeader );
        totalMessageLength += iterator->iov_len;
        iterator++;
        ioVectorLength++;

        /* Serialize the client ID. */
        vectorsAdded = addEncodedStringToVector( serializedClientIDLength,
                                                 pConnectInfo->pClientIdentifier,
                                                 pConnectInfo->clientIdentifierLength,
                                                 iterator,
                                                 &totalMessageLength );

        /* Update the iterator to point to the next empty slot. */
        iterator = &iterator[ vectorsAdded ];
        ioVectorLength += vectorsAdded;

        if( pWillInfo != NULL )
        {
            /* Serialize the topic. */
            vectorsAdded = addEncodedStringToVector( serializedTopicLength,
                                                     pWillInfo->pTopicName,
                                                     pWillInfo->topicNameLength,
                                                     iterator,
                                                     &totalMessageLength );

            /* Update the iterator to point to the next empty slot. */
            iterator = &iterator[ vectorsAdded ];
            ioVectorLength += vectorsAdded;


            /* Serialize the payload. Payload of last will and testament can be NULL. */
            vectorsAdded = addEncodedStringToVector( serializedPayloadLength,
                                                     pWillInfo->pPayload,
                                                     ( uint16_t ) pWillInfo->payloadLength,
                                                     iterator,
                                                     &totalMessageLength );

            /* Update the iterator to point to the next empty slot. */
            iterator = &iterator[ vectorsAdded ];
            ioVectorLength += vectorsAdded;
        }

        /* Encode the user name if provided. */
        if( pConnectInfo->pUserName != NULL )
        {
            /* Serialize the user name string. */
            vectorsAdded = addEncodedStringToVector( serializedUsernameLength,
                                                     pConnectInfo->pUserName,
                                                     pConnectInfo->userNameLength,
                                                     iterator,
                                                     &totalMessageLength );

            /* Update the iterator to point to the next empty slot. */
            iterator = &iterator[ vectorsAdded ];
            ioVectorLength += vectorsAdded;
        }

        /* Encode the password if provided. */
        if( pConnectInfo->pPassword != NULL )
        {
            /* Serialize the user name string. */
            vectorsAdded = addEncodedStringToVector( serializedPasswordLength,
                                                     pConnectInfo->pPassword,
                                                     pConnectInfo->passwordLength,
                                                     iterator,
                                                     &totalMessageLength );
            /* Update the iterator to point to the next empty slot. */
            iterator = &iterator[ vectorsAdded ];
            ioVectorLength += vectorsAdded;
        }

        bytesSentOrError = sendMessageVector( pContext, pIoVector, ioVectorLength );

        if( bytesSentOrError != ( int32_t ) totalMessageLength )
        {
            status = MQTTSendFailed;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnack( const MQTTContext_t * pContext,
                                    uint32_t timeoutMs,
                                    bool cleanSession,
                                    MQTTPacketInfo_t * pIncomingPacket,
                                    bool * pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;
    bool breakFromLoop = false;
    uint16_t loopCount = 0U;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->getTime != NULL );

    getTimeStamp = pContext->getTime;

    /* Get the entry time for the function. */
    entryTimeMs = getTimeStamp();

    do
    {
        /* Transport read for incoming CONNACK packet type and length.
         * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
         * returned after a transport receive timeout, an error, or a successful
         * receive of packet type and length. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.pNetworkContext,
                                                      pIncomingPacket );

        /* The loop times out based on 2 conditions.
         * 1. If timeoutMs is greater than 0:
         *    Loop times out based on the timeout calculated by getTime()
         *    function.
         * 2. If timeoutMs is 0:
         *    Loop times out based on the maximum number of retries config
         *    MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT. This config will control
         *    maximum the number of retry attempts to read the CONNACK packet.
         *    A value of 0 for the config will try once to read CONNACK. */
        if( timeoutMs > 0U )
        {
            breakFromLoop = calculateElapsedTime( getTimeStamp(), entryTimeMs ) >= timeoutMs;
        }
        else
        {
            breakFromLoop = loopCount >= MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT;
            loopCount++;
        }

        /* Loop until there is data to read or if we have exceeded the timeout/retries. */
    } while( ( status == MQTTNoDataAvailable ) && ( breakFromLoop == false ) );

    if( status == MQTTSuccess )
    {
        /* Time taken in this function so far. */
        timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

        if( timeTakenMs < timeoutMs )
        {
            /* Calculate remaining time for receiving the remainder of
             * the packet. */
            remainingTimeMs = timeoutMs - timeTakenMs;
        }

        /* Reading the remainder of the packet by transport recv.
         * Attempt to read once even if the timeout has expired.
         * Invoking receivePacket with remainingTime as 0 would attempt to
         * recv from network once. If using retries, the remainder of the
         * CONNACK packet is tried to be read only once. Reading once would be
         * good as the packet type and remaining length was already read. Hence,
         * the probability of the remaining 2 bytes available to read is very high. */
        if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = receivePacket( pContext,
                                    *pIncomingPacket,
                                    remainingTimeMs );
        }
        else
        {
            LogError( ( "Incorrect packet type %X received while expecting"
                        " CONNACK(%X).",
                        ( unsigned int ) pIncomingPacket->type,
                        MQTT_PACKET_TYPE_CONNACK ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Update the packet info pointer to the buffer read. */
        pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

        /* Deserialize CONNACK. */
        status = MQTT_DeserializeAck( pIncomingPacket, NULL, pSessionPresent );
    }

    /* If a clean session is requested, a session present should not be set by
     * broker. */
    if( status == MQTTSuccess )
    {
        if( ( cleanSession == true ) && ( *pSessionPresent == true ) )
        {
            LogError( ( "Unexpected session present flag in CONNACK response from broker."
                        " CONNECT request with clean session was made with broker." ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        LogDebug( ( "Received MQTT CONNACK successfully from broker." ) );
    }
    else
    {
        LogError( ( "CONNACK recv failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t handleSessionResumption( MQTTContext_t * pContext,
                                             bool sessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    MQTTPublishState_t state = MQTTStateNull;

    assert( pContext != NULL );

    /* Reset the index and clear the buffer when a new session is established. */
    pContext->index = 0;
    ( void ) memset( pContext->networkBuffer.pBuffer, 0, pContext->networkBuffer.size );

    if( sessionPresent == true )
    {
        /* Get the next packet ID for which a PUBREL need to be resent. */
        packetId = MQTT_PubrelToResend( pContext, &cursor, &state );

        /* Resend all the PUBREL acks after session is reestablished. */
        while( ( packetId != MQTT_PACKET_ID_INVALID ) &&
               ( status == MQTTSuccess ) )
        {
            status = sendPublishAcks( pContext, packetId, state );

            packetId = MQTT_PubrelToResend( pContext, &cursor, &state );
        }
    }
    else
    {
        /* Clear any existing records if a new session is established. */
        if( pContext->outgoingPublishRecordMaxCount > 0U )
        {
            ( void ) memset( pContext->outgoingPublishRecords,
                             0x00,
                             pContext->outgoingPublishRecordMaxCount * sizeof( *pContext->outgoingPublishRecords ) );
        }

        if( pContext->incomingPublishRecordMaxCount > 0U )
        {
            ( void ) memset( pContext->incomingPublishRecords,
                             0x00,
                             pContext->incomingPublishRecordMaxCount * sizeof( *pContext->incomingPublishRecords ) );
        }
    }

    return status;
}

static MQTTStatus_t validatePublishParams( const MQTTContext_t * pContext,
                                           const MQTTPublishInfo_t * pPublishInfo,
                                           uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pPublishInfo=%p.",
                    ( void * ) pContext,
                    ( void * ) pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for PUBLISH with QoS=%u.",
                    ( unsigned int ) pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->payloadLength > 0U ) && ( pPublishInfo->pPayload == NULL ) )
    {
        LogError( ( "A nonzero payload length requires a non-NULL payload: "
                    "payloadLength=%lu, pPayload=%p.",
                    ( unsigned long ) pPublishInfo->payloadLength,
                    pPublishInfo->pPayload ) );
        status = MQTTBadParameter;
    }
    else if( ( pContext->outgoingPublishRecords == NULL ) && ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        LogError( ( "Trying to publish a QoS > MQTTQoS0 packet when outgoing publishes "
                    "for QoS1/QoS2 have not been enabled. Please, call MQTT_InitStatefulQoS "
                    "to initialize and enable the use of QoS1/QoS2 publishes." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* MISRA else */
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const TransportInterface_t * pTransportInterface,
                        MQTTGetCurrentTimeFunc_t getTimeFunction,
                        MQTTEventCallback_t userCallback,
                        const MQTTFixedBuffer_t * pNetworkBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pTransportInterface == NULL ) ||
        ( pNetworkBuffer == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pTransportInterface=%p, "
                    "pNetworkBuffer=%p",
                    ( void * ) pContext,
                    ( void * ) pTransportInterface,
                    ( void * ) pNetworkBuffer ) );
        status = MQTTBadParameter;
    }
    else if( getTimeFunction == NULL )
    {
        LogError( ( "Invalid parameter: getTimeFunction is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( userCallback == NULL )
    {
        LogError( ( "Invalid parameter: userCallback is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( pTransportInterface->recv == NULL )
    {
        LogError( ( "Invalid parameter: pTransportInterface->recv is NULL" ) );
        status = MQTTBadParameter;
    }
    else if( pTransportInterface->send == NULL )
    {
        LogError( ( "Invalid parameter: pTransportInterface->send is NULL" ) );
        status = MQTTBadParameter;
    }
    else
    {
        ( void ) memset( pContext, 0x00, sizeof( MQTTContext_t ) );

        pContext->connectStatus = MQTTNotConnected;
        pContext->transportInterface = *pTransportInterface;
        pContext->getTime = getTimeFunction;
        pContext->appCallback = userCallback;
        pContext->networkBuffer = *pNetworkBuffer;

        /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
        pContext->nextPacketId = 1;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_InitStatefulQoS( MQTTContext_t * pContext,
                                   MQTTPubAckInfo_t * pOutgoingPublishRecords,
                                   size_t outgoingPublishCount,
                                   MQTTPubAckInfo_t * pIncomingPublishRecords,
                                   size_t incomingPublishCount )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p\n",
                    ( void * ) pContext ) );
        status = MQTTBadParameter;
    }

    /* Check whether the arguments make sense. Not equal here behaves
     * like an exclusive-or operator for boolean values. */
    else if( ( outgoingPublishCount == 0U ) !=
             ( pOutgoingPublishRecords == NULL ) )
    {
        LogError( ( "Arguments do not match: pOutgoingPublishRecords=%p, "
                    "outgoingPublishCount=%lu",
                    ( void * ) pOutgoingPublishRecords,
                    ( unsigned long ) outgoingPublishCount ) );
        status = MQTTBadParameter;
    }

    /* Check whether the arguments make sense. Not equal here behaves
     * like an exclusive-or operator for boolean values. */
    else if( ( incomingPublishCount == 0U ) !=
             ( pIncomingPublishRecords == NULL ) )
    {
        LogError( ( "Arguments do not match: pIncomingPublishRecords=%p, "
                    "incomingPublishCount=%lu",
                    ( void * ) pIncomingPublishRecords,
                    ( unsigned long ) incomingPublishCount ) );
        status = MQTTBadParameter;
    }
    else if( pContext->appCallback == NULL )
    {
        LogError( ( "MQTT_InitStatefulQoS must be called only after MQTT_Init has"
                    " been called successfully.\n" ) );
        status = MQTTBadParameter;
    }
    else
    {
        pContext->incomingPublishRecordMaxCount = incomingPublishCount;
        pContext->incomingPublishRecords = pIncomingPublishRecords;
        pContext->outgoingPublishRecordMaxCount = outgoingPublishCount;
        pContext->outgoingPublishRecords = pOutgoingPublishRecords;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_CancelCallback( const MQTTContext_t * pContext,
                                  uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogWarn( ( "pContext is NULL\n" ) );
        status = MQTTBadParameter;
    }
    else if( pContext->outgoingPublishRecords == NULL )
    {
        LogError( ( "QoS1/QoS2 is not initialized for use. Please, "
                    "call MQTT_InitStatefulQoS to enable QoS1 and QoS2 "
                    "publishes.\n" ) );
        status = MQTTBadParameter;
    }
    else
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        status = MQTT_RemoveStateRecord( pContext,
                                         packetId );

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };

    incomingPacket.type = ( uint8_t ) 0;

    if( ( pContext == NULL ) || ( pConnectInfo == NULL ) || ( pSessionPresent == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pConnectInfo=%p, pSessionPresent=%p.",
                    ( void * ) pContext,
                    ( void * ) pConnectInfo,
                    ( void * ) pSessionPresent ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT connect packet size and remaining length. */
        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebug( ( "CONNECT packet size is %lu and remaining length is %lu.",
                    ( unsigned long ) packetSize,
                    ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_SEND_HOOK( pContext );

        status = sendConnectWithoutCopy( pContext,
                                         pConnectInfo,
                                         pWillInfo,
                                         remainingLength );

        MQTT_POST_SEND_HOOK( pContext );
    }

    /* Read CONNACK from transport layer. */
    if( status == MQTTSuccess )
    {
        status = receiveConnack( pContext,
                                 timeoutMs,
                                 pConnectInfo->cleanSession,
                                 &incomingPacket,
                                 pSessionPresent );
    }

    if( status == MQTTSuccess )
    {
        /* Resend PUBRELs when reestablishing a session, or clear records for new sessions. */
        status = handleSessionResumption( pContext, *pSessionPresent );
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "MQTT connection established with the broker." ) );
        pContext->connectStatus = MQTTConnected;
        /* Initialize keep-alive fields after a successful connection. */
        pContext->keepAliveIntervalSec = pConnectInfo->keepAliveSeconds;
        pContext->waitingForPingResp = false;
        pContext->pingReqSendTimeMs = 0U;
    }
    else
    {
        LogError( ( "MQTT connection failed with status = %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              &remainingLength,
                                              &packetSize );
        LogDebug( ( "SUBSCRIBE packet size is %lu and remaining length is %lu.",
                    ( unsigned long ) packetSize,
                    ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        MQTT_PRE_SEND_HOOK( pContext );

        /* Send MQTT SUBSCRIBE packet. */
        status = sendSubscribeWithoutCopy( pContext,
                                           pSubscriptionList,
                                           subscriptionCount,
                                           packetId,
                                           remainingLength );

        MQTT_POST_SEND_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId )
{
    size_t headerSize = 0UL;
    size_t remainingLength = 0UL;
    size_t packetSize = 0UL;
    MQTTPublishState_t publishStatus = MQTTStateNull;
    bool stateUpdateHookExecuted = false;

    /* Maximum number of bytes required by the 'fixed' part of the PUBLISH
     * packet header according to the MQTT specifications.
     * Header byte           0 + 1 = 1
     * Length (max)            + 4 = 5
     * Topic string length     + 2 = 7
     *
     * Note that since publish is one of the most common operations in MQTT
     * connection, we have moved the topic string length to the 'fixed' part of
     * the header so efficiency. Otherwise, we would need an extra vector and
     * an extra call to 'send' (in case writev is not defined) to send the
     * topic length.    */
    uint8_t mqttHeader[ 7U ];

    /* Validate arguments. */
    MQTTStatus_t status = validatePublishParams( pContext, pPublishInfo, packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            &remainingLength,
                                            &packetSize );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeaderWithoutTopic( pPublishInfo,
                                                          remainingLength,
                                                          mqttHeader,
                                                          &headerSize );
    }

    if( ( status == MQTTSuccess ) && ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        /* Set the flag so that the corresponding hook can be called later. */
        stateUpdateHookExecuted = true;

        status = MQTT_ReserveState( pContext,
                                    packetId,
                                    pPublishInfo->qos );

        /* State already exists for a duplicate packet.
         * If a state doesn't exist, it will be handled as a new publish in
         * state engine. */
        if( ( status == MQTTStateCollision ) && ( pPublishInfo->dup == true ) )
        {
            status = MQTTSuccess;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex as multiple send calls are required for sending this
         * packet. */
        MQTT_PRE_SEND_HOOK( pContext );

        status = sendPublishWithoutCopy( pContext,
                                         pPublishInfo,
                                         mqttHeader,
                                         headerSize,
                                         packetId );

        /* Give the mutex away for the next taker. */
        MQTT_POST_SEND_HOOK( pContext );
    }

    if( ( status == MQTTSuccess ) &&
        ( pPublishInfo->qos > MQTTQoS0 ) )
    {
        /* Update state machine after PUBLISH is sent.
         * Only to be done for QoS1 or QoS2. */
        status = MQTT_UpdateStatePublish( pContext,
                                          packetId,
                                          MQTT_SEND,
                                          pPublishInfo->qos,
                                          &publishStatus );

        if( status != MQTTSuccess )
        {
            LogError( ( "Update state for publish failed with status %s."
                        " However PUBLISH packet was sent to the broker."
                        " Any further handling of ACKs for the packet Id"
                        " will fail.",
                        MQTT_Status_strerror( status ) ) );
        }
    }

    if( stateUpdateHookExecuted == true )
    {
        /* Regardless of the status, if the mutex was taken due to the
         * packet being of QoS > QoS0, then it should be relinquished. */
        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    if( status != MQTTSuccess )
    {
        LogError( ( "MQTT PUBLISH failed with status %s.",
                    MQTT_Status_strerror( status ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext )
{
    int32_t sendResult = 0;
    MQTTStatus_t status = MQTTSuccess;
    size_t packetSize = 0U;
    /* MQTT ping packets are of fixed length. */
    uint8_t pingreqPacket[ 2U ];
    MQTTFixedBuffer_t localBuffer;

    localBuffer.pBuffer = pingreqPacket;
    localBuffer.size = sizeof( pingreqPacket );

    if( pContext == NULL )
    {
        LogError( ( "pContext is NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT PINGREQ packet size. */
        status = MQTT_GetPingreqPacketSize( &packetSize );

        if( status == MQTTSuccess )
        {
            assert( packetSize == localBuffer.size );
            LogDebug( ( "MQTT PINGREQ packet size is %lu.",
                        ( unsigned long ) packetSize ) );
        }
        else
        {
            LogError( ( "Failed to get the PINGREQ packet size." ) );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT PINGREQ. */
        status = MQTT_SerializePingreq( &localBuffer );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex as the send call should not be interrupted in
         * between. */
        MQTT_PRE_SEND_HOOK( pContext );

        /* Send the serialized PINGREQ packet to transport layer.
         * Here, we do not use the vectored IO approach for efficiency as the
         * Ping packet does not have numerous fields which need to be copied
         * from the user provided buffers. Thus it can be sent directly. */
        sendResult = sendBuffer( pContext,
                                 localBuffer.pBuffer,
                                 packetSize );

        /* Give the mutex away. */
        MQTT_POST_SEND_HOOK( pContext );

        /* It is an error to not send the entire PINGREQ packet. */
        if( sendResult < ( int32_t ) packetSize )
        {
            LogError( ( "Transport send failed for PINGREQ packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            pContext->pingReqSendTimeMs = pContext->lastPacketTxTime;
            pContext->waitingForPingResp = true;
            LogDebug( ( "Sent %ld bytes of PINGREQ packet.",
                        ( long int ) sendResult ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetUnsubscribePacketSize( pSubscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
        LogDebug( ( "UNSUBSCRIBE packet size is %lu and remaining length is %lu.",
                    ( unsigned long ) packetSize,
                    ( unsigned long ) remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex because the below call should not be interrupted. */
        MQTT_PRE_SEND_HOOK( pContext );

        status = sendUnsubscribeWithoutCopy( pContext,
                                             pSubscriptionList,
                                             subscriptionCount,
                                             packetId,
                                             remainingLength );

        /* Give the mutex away. */
        MQTT_POST_SEND_HOOK( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext )
{
    size_t packetSize = 0U;
    int32_t sendResult = 0;
    MQTTStatus_t status = MQTTSuccess;
    MQTTFixedBuffer_t localBuffer;
    uint8_t disconnectPacket[ 2U ];

    localBuffer.pBuffer = disconnectPacket;
    localBuffer.size = 2U;

    /* Validate arguments. */
    if( pContext == NULL )
    {
        LogError( ( "pContext cannot be NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT DISCONNECT packet size. */
        status = MQTT_GetDisconnectPacketSize( &packetSize );
        LogDebug( ( "MQTT DISCONNECT packet size is %lu.",
                    ( unsigned long ) packetSize ) );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT DISCONNECT packet. */
        status = MQTT_SerializeDisconnect( &localBuffer );
    }

    if( status == MQTTSuccess )
    {
        /* Take the mutex because the below call should not be interrupted. */
        MQTT_PRE_SEND_HOOK( pContext );

        /* Here we do not use vectors as the disconnect packet has fixed fields
         * which do not reside in user provided buffers. Thus, it can be sent
         * using a simple send call. */
        sendResult = sendBuffer( pContext,
                                 localBuffer.pBuffer,
                                 packetSize );

        /* Give the mutex away. */
        MQTT_POST_SEND_HOOK( pContext );

        if( sendResult < ( int32_t ) packetSize )
        {
            LogError( ( "Transport send failed for DISCONNECT packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %ld bytes of DISCONNECT packet.",
                        ( long int ) sendResult ) );
        }
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "Disconnected from the broker." ) );
        pContext->connectStatus = MQTTNotConnected;

        /* Reset the index and clean the buffer on a successful disconnect. */
        pContext->index = 0;
        ( void ) memset( pContext->networkBuffer.pBuffer, 0, pContext->networkBuffer.size );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTBadParameter;

    if( pContext == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context cannot be NULL." ) );
    }
    else if( pContext->getTime == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context must have valid getTime." ) );
    }
    else if( pContext->networkBuffer.pBuffer == NULL )
    {
        LogError( ( "Invalid input parameter: The MQTT context's networkBuffer must not be NULL." ) );
    }
    else
    {
        pContext->controlPacketSent = false;
        status = receiveSingleIteration( pContext, true );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTBadParameter;

    if( pContext == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context cannot be NULL." ) );
    }
    else if( pContext->getTime == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT Context must have a valid getTime function." ) );
    }
    else if( pContext->networkBuffer.pBuffer == NULL )
    {
        LogError( ( "Invalid input parameter: MQTT context's networkBuffer must not be NULL." ) );
    }
    else
    {
        status = receiveSingleIteration( pContext, false );
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_GetPacketId( MQTTContext_t * pContext )
{
    uint16_t packetId = 0U;

    if( pContext != NULL )
    {
        MQTT_PRE_STATE_UPDATE_HOOK( pContext );

        packetId = pContext->nextPacketId;

        /* A packet ID of zero is not a valid packet ID. When the max ID
         * is reached the next one should start at 1. */
        if( pContext->nextPacketId == ( uint16_t ) UINT16_MAX )
        {
            pContext->nextPacketId = 1;
        }
        else
        {
            pContext->nextPacketId++;
        }

        MQTT_POST_STATE_UPDATE_HOOK( pContext );
    }

    return packetId;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_MatchTopic( const char * pTopicName,
                              const uint16_t topicNameLength,
                              const char * pTopicFilter,
                              const uint16_t topicFilterLength,
                              bool * pIsMatch )
{
    MQTTStatus_t status = MQTTSuccess;
    bool topicFilterStartsWithWildcard = false;
    bool matchStatus = false;

    if( ( pTopicName == NULL ) || ( topicNameLength == 0u ) )
    {
        LogError( ( "Invalid paramater: Topic name should be non-NULL and its "
                    "length should be > 0: TopicName=%p, TopicNameLength=%hu",
                    ( void * ) pTopicName,
                    ( unsigned short ) topicNameLength ) );

        status = MQTTBadParameter;
    }
    else if( ( pTopicFilter == NULL ) || ( topicFilterLength == 0u ) )
    {
        LogError( ( "Invalid paramater: Topic filter should be non-NULL and "
                    "its length should be > 0: TopicName=%p, TopicFilterLength=%hu",
                    ( void * ) pTopicFilter,
                    ( unsigned short ) topicFilterLength ) );
        status = MQTTBadParameter;
    }
    else if( pIsMatch == NULL )
    {
        LogError( ( "Invalid paramater: Output parameter, pIsMatch, is NULL" ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Check for an exact match if the incoming topic name and the registered
         * topic filter length match. */
        if( topicNameLength == topicFilterLength )
        {
            matchStatus = strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0;
        }

        if( matchStatus == false )
        {
            /* If an exact match was not found, match against wildcard characters in
             * topic filter.*/

            /* Determine if topic filter starts with a wildcard. */
            topicFilterStartsWithWildcard = ( pTopicFilter[ 0 ] == '+' ) ||
                                            ( pTopicFilter[ 0 ] == '#' );

            /* Note: According to the MQTT 3.1.1 specification, incoming PUBLISH topic names
             * starting with "$" character cannot be matched against topic filter starting with
             * a wildcard, i.e. for example, "$SYS/sport" cannot be matched with "#" or
             * "+/sport" topic filters. */
            if( !( ( pTopicName[ 0 ] == '$' ) && ( topicFilterStartsWithWildcard == true ) ) )
            {
                matchStatus = matchTopicFilter( pTopicName, topicNameLength, pTopicFilter, topicFilterLength );
            }
        }

        /* Update the output parameter with the match result. */
        *pIsMatch = matchStatus;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetSubAckStatusCodes( const MQTTPacketInfo_t * pSubackPacket,
                                        uint8_t ** pPayloadStart,
                                        size_t * pPayloadSize )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pSubackPacket == NULL )
    {
        LogError( ( "Invalid parameter: pSubackPacket is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadStart == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadStart is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pPayloadSize == NULL )
    {
        LogError( ( "Invalid parameter: pPayloadSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else if( pSubackPacket->type != MQTT_PACKET_TYPE_SUBACK )
    {
        LogError( ( "Invalid parameter: Input packet is not a SUBACK packet: "
                    "ExpectedType=%02x, InputType=%02x",
                    ( int ) MQTT_PACKET_TYPE_SUBACK,
                    ( int ) pSubackPacket->type ) );
        status = MQTTBadParameter;
    }
    else if( pSubackPacket->pRemainingData == NULL )
    {
        LogError( ( "Invalid parameter: pSubackPacket->pRemainingData is NULL" ) );
        status = MQTTBadParameter;
    }

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    else if( pSubackPacket->remainingLength < 3U )
    {
        LogError( ( "Invalid parameter: Packet remaining length is invalid: "
                    "Should be greater than 2 for SUBACK packet: InputRemainingLength=%lu",
                    ( unsigned long ) pSubackPacket->remainingLength ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* According to the MQTT 3.1.1 protocol specification, the "Remaining Length" field is a
         * length of the variable header (2 bytes) plus the length of the payload.
         * Therefore, we add 2 positions for the starting address of the payload, and
         * subtract 2 bytes from the remaining length for the length of the payload.*/
        *pPayloadStart = &pSubackPacket->pRemainingData[ sizeof( uint16_t ) ];
        *pPayloadSize = pSubackPacket->remainingLength - sizeof( uint16_t );
    }

    return status;
}

/*-----------------------------------------------------------*/

const char * MQTT_Status_strerror( MQTTStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case MQTTSuccess:
            str = "MQTTSuccess";
            break;

        case MQTTBadParameter:
            str = "MQTTBadParameter";
            break;

        case MQTTNoMemory:
            str = "MQTTNoMemory";
            break;

        case MQTTSendFailed:
            str = "MQTTSendFailed";
            break;

        case MQTTRecvFailed:
            str = "MQTTRecvFailed";
            break;

        case MQTTBadResponse:
            str = "MQTTBadResponse";
            break;

        case MQTTServerRefused:
            str = "MQTTServerRefused";
            break;

        case MQTTNoDataAvailable:
            str = "MQTTNoDataAvailable";
            break;

        case MQTTIllegalState:
            str = "MQTTIllegalState";
            break;

        case MQTTStateCollision:
            str = "MQTTStateCollision";
            break;

        case MQTTKeepAliveTimeout:
            str = "MQTTKeepAliveTimeout";
            break;

        case MQTTNeedMoreBytes:
            str = "MQTTNeedMoreBytes";
            break;

        default:
            str = "Invalid MQTT Status code";
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/
