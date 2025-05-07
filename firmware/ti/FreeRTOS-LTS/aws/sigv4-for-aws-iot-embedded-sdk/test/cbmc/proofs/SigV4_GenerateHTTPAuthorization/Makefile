# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = SigV4_GenerateHTTPAuthorization_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = SigV4_GenerateHTTPAuthorization

# Define constants so as to limit the running time of the proofs.
# Note that these constants are also deliberately chosen so as to attain
# coverage for the SigV4InsufficientMemory cases.
# For the constants below,
# SIGV4_PROCESSING_BUFFER_LENGTH is set specifically to 60.
# It may be easier to attain coverage if the processing buffer is instead
# provided by the user as the length can be variable.
# However, since the length of the processing buffer is fixed,
# these constants must also be fixed in order to match whatever
# SIGV4_PROCESSING_BUFFER_LENGTH is set to in sigv4_config.h.
MAX_QUERY_LEN=6
MAX_HEADERS_LEN=6
MAX_URI_LEN=3
MAX_REQUEST_LEN=16
S3_SERVICE_LEN=2
UNSIGNED_PAYLOAD_LEN=17
MAX_REGION_LEN=30
MAX_SERVICE_LEN=30
MAX_ALGORITHM_LEN=30
MAX_HASH_DIGEST_LEN=16
MAX_HASH_BLOCK_LEN=17
# This is the actual maximum length of an AWS access key ID
MAX_ACCESS_KEY_ID_LEN=128

DEFINES += -DMAX_QUERY_LEN=$(MAX_QUERY_LEN)
DEFINES += -DMAX_HEADERS_LEN=$(MAX_HEADERS_LEN)
DEFINES += -DMAX_URI_LEN=$(MAX_URI_LEN)
DEFINES += -DMAX_HASH_DIGEST_LEN=$(MAX_HASH_DIGEST_LEN)
DEFINES += -DMAX_HASH_BLOCK_LEN=$(MAX_HASH_BLOCK_LEN)
DEFINES += -DMAX_REGION_LEN=$(MAX_REGION_LEN)
DEFINES += -DMAX_SERVICE_LEN=$(MAX_SERVICE_LEN)
DEFINES += -DMAX_ALGORITHM_LEN=$(MAX_ALGORITHM_LEN)
DEFINES += -DMAX_ACCESS_KEY_ID_LEN=$(MAX_ACCESS_KEY_ID_LEN)
INCLUDES +=

REMOVE_FUNCTION_BODY += memcpy
REMOVE_FUNCTION_BODY += memmove
UNWINDSET += setQueryStringFieldsAndValues.0:$(MAX_QUERY_LEN)
UNWINDSET += parseHeaderKeyValueEntries.0:$(MAX_HEADERS_LEN)
UNWINDSET += lowercaseHexEncode.0:$(MAX_HASH_DIGEST_LEN)
UNWINDSET += hmacIntermediate.0:$(MAX_HASH_BLOCK_LEN)
UNWINDSET += hmacFinal.0:$(MAX_HASH_BLOCK_LEN)
UNWINDSET += strncmp.0:$(S3_SERVICE_LEN)
UNWINDSET += strlen.0:$(UNSIGNED_PAYLOAD_LEN)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/hash_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/memcpy.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/memmove.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/sigv4_stubs.c

include ../Makefile-json.common

# Substitution command to pass to sed for patching sigv4.c. The
# characters " and # must be escaped with backslash.
SIGV4_SED_EXPR = 1s/^/\#include \"sigv4_stubs.h\" /; s/^static //; s/SigV4Status_t (scanValue|SigV4_EncodeURI|generateCanonicalQuery|generateCanonicalAndSignedHeaders|copyHeaderStringToCanonicalBuffer)\b/&_/
