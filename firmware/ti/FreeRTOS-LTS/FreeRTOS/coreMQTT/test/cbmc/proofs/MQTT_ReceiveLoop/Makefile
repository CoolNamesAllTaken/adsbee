# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_ReceiveLoop_harness
PROOF_UID=MQTT_ReceiveLoop

# Bound on the timeout in MQTT_ProcessLoop. This timeout is bounded because
# memory saftey can be proven in a only a few iteration of the MQTT operations.
# Each iteration will try to receive a single packet in its entirety. With a time
# out of 2 we can get coverage of the entire function. Another iteration will
# performed unnecessarily duplicating of the proof.
MQTT_RECEIVE_TIMEOUT=3
# The NetworkInterfaceReceiveStub is called once for getting the incoming packet
# type with one byte of data, then it is called multiple times to reveive the
# packet.
MAX_NETWORK_RECV_TRIES=4
# Please see test/cbmc/stubs/network_interface_subs.c for
# more information on MAX_NETWORK_SEND_TRIES.
MAX_NETWORK_SEND_TRIES=3
# Please see test/cbmc/include/core_mqtt_config.h for more
# information.
MQTT_STATE_ARRAY_MAX_COUNT=11
DEFINES += -DMQTT_RECEIVE_TIMEOUT=$(MQTT_RECEIVE_TIMEOUT)
DEFINES += -DMAX_NETWORK_SEND_TRIES=$(MAX_NETWORK_SEND_TRIES)
DEFINES += -DMAX_NETWORK_RECV_TRIES=$(MAX_NETWORK_RECV_TRIES)
INCLUDES +=

# These functions have their memory saftey proven in other harnesses.
REMOVE_FUNCTION_BODY += MQTT_DeserializeAck
REMOVE_FUNCTION_BODY += MQTT_SerializeAck
REMOVE_FUNCTION_BODY += memmove # Use stub

# The loops below are unwound once more than the exclusive timeout bound.
UNWINDSET += __CPROVER_file_local_core_mqtt_c_discardStoredPacket.0:$(MAX_NETWORK_RECV_TRIES)
UNWINDSET += __CPROVER_file_local_core_mqtt_c_recvExact.0:$(MAX_NETWORK_RECV_TRIES)
# Unlike recvExact, sendBuffer is not bounded by the timeout. The loop in
# sendBuffer will continue until all the bytes are sent or a network error
# occurs. Please see NetworkInterfaceReceiveStub in
# libraries\standard\mqtt\cbmc\stubs\network_interface_stubs.c for more
# information.
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendBuffer.0:$(MAX_NETWORK_SEND_TRIES)
# The getRemainingLength loop is unwound 5 times because getRemainingLength()
# divides a size_t variable by 128 until it reaches zero to stop the loop.
# log128(SIZE_MAX) = 4.571...
UNWINDSET += __CPROVER_file_local_core_mqtt_serializer_c_processRemainingLength.0:5
# These loops will run for the maximum number of publishes pending acknowledgement.
# This is set in test/cbmc/include/core_mqtt_config.h.
UNWINDSET += __CPROVER_file_local_core_mqtt_state_c_addRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)
UNWINDSET += __CPROVER_file_local_core_mqtt_state_c_findInRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/event_callback_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/memmove.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_serializer.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_state.c

EXPENSIVE = true

include ../Makefile.common
