#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# the Software, and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#

HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_Connect_harness
PROOF_UID=MQTT_Connect

# Please see test/cbmc/stubs/network_interface_subs.c for
# more information on MAX_NETWORK_SEND_TRIES.
MAX_NETWORK_SEND_TRIES=3
# Bound on the timeout in receiveConnack. This timeout is bounded because
# memory saftey can be proven in a only a few iteration of the MQTT operations.
# Each iteration will try to receive a single packet in its entirety. With a
# time out of 3 we can get coverage of the entire function. Another iteration
# performed will unnecessarily duplicate the proof.
MQTT_RECEIVE_TIMEOUT=3
# The NetworkInterfaceReceiveStub is called once for getting the incoming packet
# type with one byte of data, then it is called multiple times to reveive the
# packet.
MAX_NETWORK_RECV_TRIES=4
# Please see test/cbmc/include/core_mqtt_config.h for more
# information on these defines.
MQTT_STATE_ARRAY_MAX_COUNT=11
MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT=3
CONNECT_PACKET_VECTORS = 12
DEFINES += -DMQTT_RECEIVE_TIMEOUT=$(MQTT_RECEIVE_TIMEOUT)
DEFINES += -DMAX_NETWORK_SEND_TRIES=$(MAX_NETWORK_SEND_TRIES)
DEFINES += -DMAX_NETWORK_RECV_TRIES=$(MAX_NETWORK_RECV_TRIES)
INCLUDES +=

# These functions do not coincide with the call graph of MQTT_Connect, but are
# found by CBMC during processing in logs/MQTT_Connect_harness3.txt. We remove
# the function bodies to improve coverage accuracy.
REMOVE_FUNCTION_BODY += MQTT_ProcessLoop
REMOVE_FUNCTION_BODY += MQTT_ReceiveLoop
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_mqtt_c_handleIncomingPublish
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_mqtt_c_handleKeepAlive
#REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_mqtt_c_sendMessageVector
#REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_mqtt_c_sendBuffer

# The loop below is unwound once more than the timeout. The loop below uses
# the user passed in timeout to break the loop.
UNWINDSET += __CPROVER_file_local_core_mqtt_c_discardPacket.0:$(MQTT_RECEIVE_TIMEOUT)
UNWINDSET += __CPROVER_file_local_core_mqtt_c_recvExact.0:$(MAX_NETWORK_RECV_TRIES)
# If the user passed in timeout is zero, then the loop will run until the
# MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT is reached.
UNWINDSET += __CPROVER_file_local_core_mqtt_c_receiveConnack.0:$(MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT)
# Unlike recvExact, sendBuffer is not bounded by the timeout. The loop in
# sendBuffer will continue until all the bytes are sent or a network error
# occurs. Please see NetworkInterfaceReceiveStub in
# libraries\standard\mqtt\cbmc\stubs\network_interface_stubs.c for more
# information.
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendBuffer.0:$(MAX_NETWORK_SEND_TRIES)
# The loops are unwound 5 times because these functions divides a size_t
# variable by 128 until it reaches zero to stop the loop.
# log128(SIZE_MAX) = 4.571...
UNWINDSET += __CPROVER_file_local_core_mqtt_serializer_c_encodeRemainingLength.0:5
UNWINDSET += __CPROVER_file_local_core_mqtt_serializer_c_getRemainingLength.0:5
# This loop will run for the maximum number of publishes pending
# acknowledgements plus one. This value is set in
# test/cbmc/include/core_mqtt_config.h.
UNWINDSET += __CPROVER_file_local_core_mqtt_state_c_stateSelect.0:$(MQTT_STATE_ARRAY_MAX_COUNT)
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.0:${CONNECT_PACKET_VECTORS}
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.1:${CONNECT_PACKET_VECTORS}
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.2:${CONNECT_PACKET_VECTORS}

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/event_callback_stub.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_serializer.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_state.c

EXPENSIVE = true

include ../Makefile.common
