#!/bin/bash

# Default source file
SRC="./demotest/main.ll"
if [ -n "$1" ]; then
  SRC="$1"
fi

DST="${SRC%.ll}.cbe.c"

../build-cbe/bin/llvm-cbe "$SRC" && clang-format -i "$DST"

echo "Lifted LLVM IR ($SRC) -> CBE C source ($DST)"