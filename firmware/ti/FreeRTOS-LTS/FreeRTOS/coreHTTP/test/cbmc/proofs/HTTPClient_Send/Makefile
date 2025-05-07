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

HARNESS_ENTRY=HTTPClient_Send_harness
PROOF_UID=HTTPClient_Send
HARNESS_FILE=$(HARNESS_ENTRY)

DEFINES +=
INCLUDES +=

# We remove these function bodies so that they aren't categorized as possible
# function pointer targets, leading to faster execution time.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_findHeaderFieldParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_findHeaderValueParserCallback
# The memory safety of the http-parser callbacks are proven separately. The
# proofs for the functions below must have assumptions that are satisfied by the
# calling context in HTTPClient_Send.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnBodyCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnHeaderFieldCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnHeaderValueCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnStatusCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnStatusCompleteCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnHeadersCompleteCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnMessageBeginCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpParserOnMessageCompleteCallback

# Remove any unused functions for http parser
REMOVE_FUNCTION_BODY += llhttp_init
REMOVE_FUNCTION_BODY += llhttp_settings_init

# These functions are removed and replace with stubs that check that the
# destination parameter is writeable and that the source parameter is readable.
# This decreases the run-time of the proof. This is safe to do for this proof
# because all of the functions, in HTTPClient_Send, that would have used the
# results of the copy are stubbed out to be proven separately.
REMOVE_FUNCTION_BODY += strncpy
REMOVE_FUNCTION_BODY += __CPROVER_file_local_core_http_client_c_httpHeaderStrncpy

# There is a total of 10 digits in INT32_MAX. These loops are unwound once more
# than the total possible iterations in the int32_t to ASCII converation.
UNWINDSET += __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.0:11
UNWINDSET += __CPROVER_file_local_core_http_client_c_convertInt32ToAscii.1:11
UNWINDSET += HTTPClient_ReceiveAndParseHttpResponse.0:10
UNWINDSET += HTTPClient_SendHttpData.0:10

# strncmp is used to find if there exists "\r\n\r\n" at the end of the header
# buffer. Therefore, we need to unwind strncmp to the length of "\r\n\r\n" + 1.
UNWINDSET += strncmp.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/http_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/HTTPClient_Send_llhttp_execute.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/transport_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/strncpy.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/httpHeaderStrncpy.c

PROJECT_SOURCES += $(SRCDIR)/source/core_http_client.c

EXTERNAL_SAT_SOLVER := kissat

include ../Makefile.common
