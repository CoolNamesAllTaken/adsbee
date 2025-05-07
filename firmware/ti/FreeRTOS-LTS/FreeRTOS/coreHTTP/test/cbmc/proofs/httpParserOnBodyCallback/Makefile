# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY=httpParserOnBodyCallback_harness
PROOF_UID=httpParserOnBodyCallback
HARNESS_FILE=$(HARNESS_ENTRY)

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY += memmove

UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/http_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/memmove.c

PROJECT_SOURCES += $(SRCDIR)/source/core_http_client.c

EXTERNAL_SAT_SOLVER := kissat

include ../Makefile.common
