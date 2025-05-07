# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

PROOF_UID=skipString
CHECK_FUNCTION_CONTRACTS = $(PROOF_UID)
HARNESS_FILE= $(PROOF_UID)_harness

APPLY_LOOP_CONTRACTS = 1
USE_DYNAMIC_FRAMES = 1

CBMC_OBJECT_BITS = 10

USE_EXTERNAL_SAT_SOLVER ?= --external-sat-solver cadical

USE_FUNCTION_CONTRACTS += skipEscape
USE_FUNCTION_CONTRACTS += skipUTF8

include ../Makefile-json.common
