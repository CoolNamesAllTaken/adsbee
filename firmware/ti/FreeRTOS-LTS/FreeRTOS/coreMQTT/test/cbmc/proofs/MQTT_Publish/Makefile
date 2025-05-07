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
HARNESS_FILE=MQTT_Publish_harness
PROOF_UID=MQTT_Publish

# Please see test/cbmc/stubs/network_interface_subs.c for
# more information on MAX_NETWORK_SEND_TRIES.
MAX_NETWORK_SEND_TRIES=3
# Please see test/cbmc/include/core_mqtt_config.h for more
# information.
MQTT_STATE_ARRAY_MAX_COUNT=11
PUBLISH_PACKET_VECTORS = 5

DEFINES += -DMAX_NETWORK_SEND_TRIES=$(MAX_NETWORK_SEND_TRIES)
INCLUDES +=

REMOVE_FUNCTION_BODY +=
REMOVE_FUNCTION_BODY +=
# These loops will run for the maximum number of publishes pending acknowledgement.
# This is set in test/cbmc/include/core_mqtt_config.h.
UNWINDSET += __CPROVER_file_local_core_mqtt_state_c_addRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)
UNWINDSET += __CPROVER_file_local_core_mqtt_state_c_findInRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)
# The encodeRemainingLength loop is unwound 5 times because encodeRemainingLength()
# divides a size_t variable by 128 until it reaches zero to stop the loop.
# log128(SIZE_MAX) = 4.571...
UNWINDSET += __CPROVER_file_local_core_mqtt_serializer_c_encodeRemainingLength.0:5
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.0:${PUBLISH_PACKET_VECTORS}
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.1:${PUBLISH_PACKET_VECTORS}
UNWINDSET += __CPROVER_file_local_core_mqtt_c_sendMessageVector.2:${PUBLISH_PACKET_VECTORS}

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/event_callback_stub.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_serializer.c
PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_state.c

include ../Makefile.common
