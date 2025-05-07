# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY=findHeaderFieldParserCallback_harness
PROOF_UID=findHeaderFieldParserCallback
HARNESS_FILE=$(HARNESS_ENTRY)

# The header field length is bounded, so strncasecmp can be unwound to an expected
# amount that won't make the proof run too long.
MAX_HEADER_FIELD_LENGTH=11

DEFINES += -DMAX_HEADER_FIELD_LENGTH=$(MAX_HEADER_FIELD_LENGTH)
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += __CPROVER_file_local_core_http_client_c_caseInsensitiveStringCmp.0:$(MAX_HEADER_FIELD_LENGTH)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/source/core_http_client.c

EXTERNAL_SAT_SOLVER := kissat

include ../Makefile.common
