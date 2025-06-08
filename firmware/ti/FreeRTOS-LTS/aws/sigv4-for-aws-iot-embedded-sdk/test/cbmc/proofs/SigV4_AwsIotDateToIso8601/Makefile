# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = SigV4_AwsIotDateToIso8601_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = SigV4_AwsIotDateToIso8601

DEFINES += -DSIGV4_DO_NOT_USE_CUSTOM_CONFIG=1
INCLUDES +=

MONTH_ASCII_LEN=3
ISO_YEAR_LEN=5
MONTHS_IN_YEAR=12
FORMAT_RFC_5322_LEN=32

REMOVE_FUNCTION_BODY +=
UNWINDSET += parseDate.0:$(FORMAT_RFC_5322_LEN)
UNWINDSET += scanValue.0:$(ISO_YEAR_LEN)
UNWINDSET += intToAscii.0:$(ISO_YEAR_LEN)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/sigv4_stubs.c

include ../Makefile-json.common

# Substitution command to pass to sed for patching sigv4.c. The
# characters " and # must be escaped with backslash.
SIGV4_SED_EXPR = 1s/^/\#include \"sigv4_stubs.h\" /; s/^static //; s/SigV4Status_t scanValue\b/&_/
