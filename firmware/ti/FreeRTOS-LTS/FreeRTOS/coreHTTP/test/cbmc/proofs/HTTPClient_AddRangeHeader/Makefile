#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# the Software, and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#

HARNESS_ENTRY=HTTPClient_AddRangeHeader_harness
PROOF_UID=HTTPClient_AddRangeHeader
HARNESS_FILE=$(HARNESS_ENTRY)

DEFINES +=
INCLUDES +=

# These functions are removed and replace with stubs that check that the
# destination parameter is writeable and that the source parameter is readable.
# This decreases the run-time of the proof. This is safe to do for this proof
# because HTTPClient_AddRangeHeader does not use the results of the copy later
# in the function.
REMOVE_FUNCTION_BODY += strncpy
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpHeaderStrncpy

# strncmp is used to find if there exists "\r\n\r\n" at the end of the header
# buffer. Therefore, we need to unwind strncmp the length of "\r\n\r\n" + 1.
UNWINDSET += strncmp.0:5
# Maximum value of a 32 bit signed integer is 2,147,483,647, which is 10 digits.
UNWINDSET += __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.0:11
UNWINDSET += __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.1:11

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/http_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/strncpy.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/httpHeaderStrncpy.c

PROJECT_SOURCES += $(SRCDIR)/source/core_http_client.c

EXTERNAL_SAT_SOLVER := kissat

include ../Makefile.common
