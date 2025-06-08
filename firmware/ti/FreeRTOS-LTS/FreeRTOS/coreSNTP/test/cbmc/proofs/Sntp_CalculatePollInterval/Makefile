# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = Sntp_CalculatePollInterval_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = Sntp_CalculatePollInterval

# Bound for loop unwinding for loop in Sntp_CalculatePollInterval function. Unwinding
# the loop 33 times will be enough as the unsigned 32 integer can take value upto 2^32.
MAX_BOUND_FOR_LOOP=33

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += Sntp_CalculatePollInterval.0:$(MAX_BOUND_FOR_LOOP)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/core_sntp_serializer.c

include ../Makefile.common
