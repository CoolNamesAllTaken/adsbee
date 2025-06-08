/*
 * coreMQTT v2.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_mqtt_config.h
 * @brief This header sets configuration macros for the MQTT library.
 */
#ifndef CORE_MQTT_CONFIG_H_
#define CORE_MQTT_CONFIG_H_

/**
 * @brief Determines the maximum number of MQTT PUBLISH messages, pending
 * acknowledgement at a time, that are supported for incoming and outgoing
 * direction of messages, separately.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowledgement from the server before
 * they can be completed. While they are awaiting the acknowledgement, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains, separately, for both incoming and outgoing direction of
 * PUBLISHes.
 *
 * @note This definition must exist in order to compile. 10U is a typical value
 * used in the MQTT demos.
 */
#define MQTT_STATE_ARRAY_MAX_COUNT              ( 10U )

/**
 * @brief Retry count for reading CONNACK from network.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect() is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 */
#define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 2U )

/**
 * @brief Number of milliseconds to wait for a ping response to a ping
 * request as part of the keep-alive mechanism.
 *
 * If a ping response is not received before this timeout, then
 * #MQTT_ProcessLoop will return #MQTTKeepAliveTimeout.
 */
#define MQTT_PINGRESP_TIMEOUT_MS                ( 5000U )

/**
 * @brief The maximum duration of receiving no data over network when
 * attempting to read an incoming MQTT packet by the #MQTT_ProcessLoop or
 * #MQTT_ReceiveLoop API functions.
 *
 * When an incoming MQTT packet is detected, the transport receive function
 * may be called multiple times until all the expected number of bytes for the
 * packet are received. This timeout represents the maximum duration of polling
 * for any data to be received over the network for the incoming.
 * If the timeout expires, the #MQTT_ProcessLoop or #MQTT_ReceiveLoop functions
 * return #MQTTRecvFailed.
 *
 * This is set to 1 to exit right away after a zero is received in the transport
 * receive stub. There is no added value, in proving memory safety, to repeat
 * the logic that checks if the polling timeout is reached.
 */
#define MQTT_RECV_POLLING_TIMEOUT_MS            ( 1U )

#endif /* ifndef CORE_MQTT_CONFIG_H_ */
