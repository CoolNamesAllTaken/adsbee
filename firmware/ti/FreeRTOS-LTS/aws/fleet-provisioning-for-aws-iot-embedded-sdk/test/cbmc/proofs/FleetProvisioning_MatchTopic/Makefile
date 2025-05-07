# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY = harness
HARNESS_FILE = FleetProvisioning_MatchTopic_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = FleetProvisioning_MatchTopic

# The topic length is bounded to reduce the proof run time. Memory safety on the
# buffer holding the topic string can be proven within a reasonable bound. It
# adds no value to the proof to input the largest possible topic string accepted
# by AWS (64KB).
TOPIC_STRING_LENGTH_MAX=200

DEFINES += -DTOPIC_STRING_LENGTH_MAX=$(TOPIC_STRING_LENGTH_MAX)
INCLUDES +=

REMOVE_FUNCTION_BODY +=

# The longest strncmp is against FLEET_PROVISIONING_CREATE_CERTIFICATE_FROM_CSR_API_PREFIX
# length of which is 35. We unwind one more time than the bridge length.
FLEET_PROVISIONING_API_BRIDGE_LENGTH=36
UNWINDSET += strncmp.0:$(FLEET_PROVISIONING_API_BRIDGE_LENGTH)

# Enough to unwind the consumeTemplateName loop TOPIC_STRING_LENGTH_MAX times
# as template name in the topic string can not be longer than the topic string
# length.
UNWINDSET += __CPROVER_file_local_fleet_provisioning_c_consumeTemplateName.0:$(TOPIC_STRING_LENGTH_MAX)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/fleet_provisioning.c

include ../Makefile.common
