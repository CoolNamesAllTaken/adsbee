# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

PROOF_UID=JSON_SearchConst
CHECK_FUNCTION_CONTRACTS = $(PROOF_UID)
HARNESS_FILE= $(PROOF_UID)_harness

APPLY_LOOP_CONTRACTS = 1
USE_DYNAMIC_FRAMES = 1

CBMC_OBJECT_BITS = 11

USE_EXTERNAL_SAT_SOLVER ?= --external-sat-solver kissat

USE_FUNCTION_CONTRACTS += multiSearch

include ../Makefile-json.common
