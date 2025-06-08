# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = copyHeaderStringToCanonicalBuffer_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = copyHeaderStringToCanonicalBuffer

# This value was experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=10
MAX_HASH_BLOCK_LEN=17
MAX_HASH_DIGEST_LEN=16

DEFINES += -DMAX_HASH_BLOCK_LEN=$(MAX_HASH_BLOCK_LEN)
DEFINES += -DCBMC_MAX_BUFSIZE=$(CBMC_MAX_BUFSIZE)
DEFINES += -DMAX_HASH_DIGEST_LEN=$(MAX_HASH_DIGEST_LEN)
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=copyHeaderStringToCanonicalBuffer.0:$(CBMC_MAX_BUFSIZE)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile-json.common

# Substitution command to pass to sed for patching sigv4.c. The
# characters " and # must be escaped with backslash.
SIGV4_SED_EXPR = s/^static //
