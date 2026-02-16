#!/bin/bash

# Default source file
SRC="./demotest/main.ll"
if [ -n "$1" ]; then
  SRC="$1"
fi

DST="${SRC%.ll}.cbe.c"

../build-cbeoriginal/bin/llvm-cbe "$SRC" && clang-format -i "$DST"
