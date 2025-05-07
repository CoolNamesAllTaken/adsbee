# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY=httpParserOnMessageCompleteCallback_harness
PROOF_UID=httpParserOnMessageCompleteCallback
HARNESS_FILE=$(HARNESS_ENTRY)

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/source/core_http_client.c

EXTERNAL_SAT_SOLVER := kissat

include ../Makefile.common
