#!/bin/sh

UNWIND_COUNT=${UNWIND_COUNT:-10}

JobsSourceDir="../../source"
coreJSONSourceDir="coreJSON/source"
OTAJobParserSourceDir="../../source/otaJobParser"

#If coreJSON not found, clone it
if [ ! -d "coreJSON" ]; then
    git clone https://github.com/FreeRTOS/coreJSON.git --depth 1 --branch v3.2.0
fi

exec cbmc proofs.c $JobsSourceDir/jobs.c  stubs/strnlen.c \
     stubs/JSON_Validate.c stubs/JSON_SearchConst.c \
     $OTAJobParserSourceDir/job_parser.c $OTAJobParserSourceDir/ota_job_handler.c \
     -I $JobsSourceDir/include -I $coreJSONSourceDir/include \
     -I $OTAJobParserSourceDir/include -I include  \
     --unwindset strnAppend.0:26 --unwindset strnEq.0:26 \
     --unwindset matchIdApi.0:84 --unwindset isValidID.0:65 \
     --unwindset strlen.0:51 --unwindset strncpy.0:16 \
     --bounds-check --pointer-check --memory-cleanup-check --div-by-zero-check \
     --signed-overflow-check --unsigned-overflow-check --pointer-overflow-check \
     --conversion-check --undefined-shift-check --enum-range-check \
     --pointer-primitive-check --drop-unused-functions --nondet-static \
     --unwinding-assertions --c99 "$@" --unwind "$UNWIND_COUNT" --json-ui  \
     -DUNWIND_COUNT="$UNWIND_COUNT" >&1 | tee output/latest/html/run.json
