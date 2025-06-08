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


HARNESS_ENTRY=harness
HARNESS_FILE=_Cellular_TimeoutAtcmdDataSendSuccessToken_harness
PROOF_UID = _Cellular_TimeoutAtcmdDataSendSuccessToken

REMOVE_FUNCTION_BODY += _Cellular_AtParseInit
REMOVE_FUNCTION_BODY += _Cellular_PktioSendAtCmd
REMOVE_FUNCTION_BODY += __CPROVER_file_local_cellular_pkthandler_c__Cellular_DataSendWithTimeoutDelayRaw

DEFINES +=
INCLUDES +=


PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/cellular_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/global_state_cellular.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/cellular_platform.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/cellular_modules.c
PROJECT_SOURCES += $(SRCDIR)/source/cellular_common_api.c
PROJECT_SOURCES += $(SRCDIR)/source/cellular_common.c

include ../Makefile.common
