#!/bin/bash

# Default source file
SRC="./demotest/main.ll"
if [ -n "$1" ]; then
  SRC="$1"
fi

# Default destination file (same name with .ll)
DST="${SRC%.ll}.ll"
if [ -n "$2" ]; then
  DST="$2"
fi

./bin/opt -S -passes=mem2reg "$SRC" -o "$DST"
