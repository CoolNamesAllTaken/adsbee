#!/bin/bash -eu

# Copy the fuzzer executable to $OUT/
$CC $CFLAGS $LIB_FUZZING_ENGINE \
  $SRC/corejson/.clusterfuzzlite/validate_fuzzer.c \
  $SRC/corejson/source/core_json.c \
  -I$SRC/corejson/source/include \
  -o $OUT/validate_fuzzer
