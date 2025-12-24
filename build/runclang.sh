#!/bin/bash

# Default source file
SRC="./demotest/main.c"
if [ -n "$2" ]; then
  SRC="$2"
fi

DST="${SRC%.c}.ll"

if [ "$1" == "optnone" ]; then
  ./bin/clang -v -S -emit-llvm -fno-discard-value-names -O0 -Xclang -disable-O0-optnone "$SRC" -o "$DST"
else
  ./bin/clang -v -S -emit-llvm -fno-discard-value-names -O0 "$SRC" -o "$DST"
fi
