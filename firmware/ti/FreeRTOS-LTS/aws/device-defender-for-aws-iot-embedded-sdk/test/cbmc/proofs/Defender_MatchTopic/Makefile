# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY=harness
HARNESS_FILE=Defender_MatchTopic_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = Defender_MatchTopic

# The topic length is bounded to reduce the proof run time. Memory safety on the
# buffer holding the topic string can be proven within a reasonable bound. It
# adds no value to the proof to input the largest possible topic string accepted
# by AWS (64KB).
TOPIC_STRING_LENGTH_MAX=200

DEFINES += -DTOPIC_STRING_LENGTH_MAX=$(TOPIC_STRING_LENGTH_MAX)
INCLUDES +=

REMOVE_FUNCTION_BODY +=

# The longest strncmp is in matchBridge function which matches DEFENDER_API_BRIDGE
# length of which is 19. We unwind one more time than the bridge length.
DEFENDER_API_BRIDGE_LENGTH=20
UNWINDSET += strncmp.0:$(DEFENDER_API_BRIDGE_LENGTH)

# Enough to unwind the extractThingNameLength loop TOPIC_STRING_LENGTH_MAX times
# as thingname in the topic string can not be longer than the topic string
# length.
UNWINDSET += __CPROVER_file_local_defender_c_extractThingNameLength.0:$(TOPIC_STRING_LENGTH_MAX)

# Total defender APIs are 6:
# DefenderJsonReportPublish
# DefenderJsonReportAccepted
# DefenderJsonReportRejected
# DefenderCborReportPublish
# DefenderCborReportAccepted
# DefenderCborReportRejected
#
# We unwind one more than the total API count.
DEFENDER_API_COUNT=7
UNWINDSET += __CPROVER_file_local_defender_c_matchApi.0:$(DEFENDER_API_COUNT)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/defender.c

include ../Makefile.common
